module

public import FormalResearch.ModularBootstrap.Spin.SpinMomentSources
public import FormalResearch.ModularBootstrap.Upper.Rigidity.Sigma
public import FormalResearch.ModularBootstrap.Upper.Assembly.FarFirstSite
public import FormalResearch.ModularBootstrap.Upper.Assembly.Wire

/-!
# `sd:spinmoment` (Theorem SD-M2): Airy limit of the spin second-moment measure

This module completes work package `SPIN-M` for Paper II (`spinning_airy_moment.tex`, Theorem
`sd:spinmoment`, and `spinning_airy_moment_proof.tex`):

* `spinMoment_vagueLimit` (`sd:spinmoment-limit`):
  `spinMomentSpectralMeasure (cSeq j - 1) (meas j).ν` converges vaguely to
  `spinMomentVStar • airyMeasure`, with `spinMomentVStar = 2 * xiStar ^ 3 / (3 * π)`.
* `spinMoment_cluster_ratio_tendsto` (`sd:spinmoment-ratio`):
  for any bounded set `I` isolating a single Airy zero `airyNode k ∈ interior I`, the ratio of the
  spin-moment spectral mass on `I` to the scalar radial spectral mass on `I` tends to
  `spinMomentVStar`.

The proof packages the weight-5 pairing upper bound `spinMoment_window_pair_limsup_le` into
`DesignPropertyP` for the normalised moment measures `spinMomentVStar⁻¹ • spinMomentSpectralMeasure`
on `designClass ∪ displacedClassX` (adding a compactly supported continuous tent bump far beyond the
spectral support so the `DesignTest` crossing equality holds without affecting the measure integral,
positivity below `θ_j`, or compact convergence), then applies `theorem_Sigma` together with the
already formalised window families `sameSiteFamily_designClass_exists`, `displacedFamily_exists`,
and `farFamily`.
-/

@[expose] public section

open Real MeasureTheory Filter Topology Set
open scoped Real ENNReal

namespace FormalResearch.ModularBootstrap.Spin

open FormalResearch.Special
open FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.Upper.Comb
open FormalResearch.ModularBootstrap.Upper.Design
open FormalResearch.ModularBootstrap.Upper.Holes
open FormalResearch.ModularBootstrap.Upper.Membership
open FormalResearch.ModularBootstrap.Upper.Positivity
open FormalResearch.ModularBootstrap.Upper.Bump
open FormalResearch.ModularBootstrap.Upper.Window
open FormalResearch.ModularBootstrap.Upper.Window.Cardy
open FormalResearch.ModularBootstrap.Upper.Assembly
open FormalResearch.ModularBootstrap.Upper.Rigidity

/-! ### Continuous tent bump for `DesignTest` crossing normalization -/

private noncomputable def tentFn (x : ℝ) : ℝ := max 0 (1 - |x|)

private lemma continuous_tentFn : Continuous tentFn :=
  continuous_const.max (continuous_const.sub continuous_abs)

private lemma tentFn_nonneg (x : ℝ) : 0 ≤ tentFn x := le_max_left 0 _

private lemma tentFn_eq_zero_of_one_le {x : ℝ} (hx : 1 ≤ |x|) : tentFn x = 0 :=
  max_eq_left (by linarith)

private lemma tentFn_eq_zero_of_le_neg_one {x : ℝ} (hx : x ≤ -1) : tentFn x = 0 :=
  tentFn_eq_zero_of_one_le (by rw [abs_of_nonpos (by linarith)]; linarith)

private lemma hasCompactSupport_tentFn : HasCompactSupport tentFn := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -1) (b := 1)) fun x hx => ?_
  apply tentFn_eq_zero_of_one_le
  by_contra hlt
  push Not at hlt
  exact hx ⟨(abs_lt.mp hlt).1.le, (abs_lt.mp hlt).2.le⟩

private lemma integrable_tentFn : Integrable tentFn :=
  continuous_tentFn.integrable_of_hasCompactSupport hasCompactSupport_tentFn

private lemma integral_tentFn : ∫ x : ℝ, tentFn x = 1 := by
  have hi : ∫ x in (-1 : ℝ)..1, tentFn x = ∫ x : ℝ, tentFn x := by
    refine intervalIntegral.integral_eq_integral_of_support_subset (fun x hx => ?_)
    by_contra hm
    exact hx (tentFn_eq_zero_of_one_le (by
      rw [Set.mem_Ioc, not_and_or, not_lt, not_le] at hm
      rcases hm with h | h
      · rw [abs_of_nonpos (by linarith)]; linarith
      · rw [abs_of_nonneg (by linarith)]; linarith))
  rw [← hi]
  have hi0 : (∫ x in (-1 : ℝ)..1, tentFn x) =
      (∫ x in (-1 : ℝ)..0, tentFn x) + (∫ x in (0 : ℝ)..1, tentFn x) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (continuous_tentFn.intervalIntegrable (-1) 0)
      (continuous_tentFn.intervalIntegrable 0 1)).symm
  have hl : ∫ x in (-1 : ℝ)..0, tentFn x = 1 / 2 := by
    have heq : EqOn tentFn (fun x => 1 + x) (uIcc (-1) 0) := by
      intro x hx
      rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 0)] at hx
      have h0 : 0 ≤ 1 - |x| := by
        rw [abs_of_nonpos hx.2]; linarith [hx.1]
      unfold tentFn
      rw [max_eq_right h0, abs_of_nonpos hx.2]
      ring
    rw [intervalIntegral.integral_congr heq]
    have hf : ∀ x : ℝ, HasDerivAt (fun y : ℝ => y + y ^ 2 / 2) (1 + x) x := fun x => by
      simpa using (hasDerivAt_id' x).fun_add ((hasDerivAt_pow 2 x).div_const 2)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hf x)
      ((continuous_const.add continuous_id).intervalIntegrable _ _)]
    norm_num
  have hr : ∫ x in (0 : ℝ)..1, tentFn x = 1 / 2 := by
    have heq : EqOn tentFn (fun x => 1 - x) (uIcc 0 1) := by
      intro x hx
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
      have h0 : 0 ≤ 1 - |x| := by
        rw [abs_of_nonneg hx.1]; linarith [hx.2]
      unfold tentFn
      rw [max_eq_right h0, abs_of_nonneg hx.1]
    rw [intervalIntegral.integral_congr heq]
    have hf : ∀ x : ℝ, HasDerivAt (fun y : ℝ => y - y ^ 2 / 2) (1 - x) x := fun x => by
      simpa using (hasDerivAt_id' x).fun_sub ((hasDerivAt_pow 2 x).div_const 2)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hf x)
      ((continuous_const.sub continuous_id).intervalIntegrable _ _)]
    norm_num
  rw [hi0, hl, hr]
  norm_num

/-! ### Volume integrability and Virasoro/weight-5 test properties -/

private lemma virasoro_bump_integrable {c' C_g : ℝ} (hc' : 0 < c')
    (ha : virasoroProblem.totalShift ≤ c' / 12) (hCg : 0 ≤ C_g) {g : ℝ → ℝ}
    (hcont : ContinuousOn g (Ici 0))
    (hdec : ∀ t : ℝ, 0 ≤ t → |g t| ≤ C_g * Real.exp (-4 * π * √(c' / 12 * t) - π * √(3 * t / c'))) :
    Integrable (psiAiry virasoroProblem c' g) := by
  rw [integrable_psiAiry_iff virasoroProblem hc' g]
  have ha0 : 0 ≤ c' / 12 := by positivity
  let f : ℝ → ℝ := fun t => g t * virasoroProblem.cardyV (c' / 12) t
  have hf_cont : ContinuousOn f (Icc 0 1) :=
    (hcont.mono Icc_subset_Ici_self).mul
      ((continuous_cardyV virasoroProblem (c' / 12)).continuousOn)
  have hloc : IntegrableOn f (Ioc 0 1) :=
    hf_cont.integrableOn_compact isCompact_Icc |>.mono_set Ioc_subset_Icc_self
  have hδ_pos : 0 < π * √(3 / c') := by positivity
  obtain ⟨C_δ, hC_δ, hδ_bd⟩ := rpow_neg_six_le_exp_neg_sqrt hδ_pos
  have htail_dom : IntegrableOn (fun t : ℝ => (C_g * C_δ) * t ^ (-2 : ℝ)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) zero_lt_one).const_mul (C_g * C_δ)
  obtain ⟨C₁, hC₁_pos, hK₁⟩ := cardyV_le_sub_exp (w := 1) le_rfl ha0
  have hK₁' : ∀ t : ℝ, 0 ≤ t → virasoroProblem.cardyV (c' / 12) t ≤ C₁ * Real.exp (4 * π * √(c' / 12 * t)) :=
    fun t ht => by
      have h1 := WeightAxioms.cardyV_le_kernelK virasoroProblem ha ht
      have h2 := hK₁ t ht
      simp only [Nat.sub_self, pow_zero, mul_one] at h2
      exact h1.trans h2
  have htail : IntegrableOn f (Ioi 1) := by
    refine htail_dom.const_mul C₁ |>.mono' ?_ ?_
    · exact ((hcont.mono (Ioi_subset_Ici zero_le_one)).mul
        ((continuous_cardyV virasoroProblem (c' / 12)).continuousOn)).aestronglyMeasurable
        measurableSet_Ioi
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
      have ht1 : 1 < t := ht
      have ht0 : 0 ≤ t := by linarith
      have hV_nn : 0 ≤ virasoroProblem.cardyV (c' / 12) t := virasoroProblem.cardyV_nonneg ha ht0
      have hV_le := hK₁' t ht0
      have hg_le := hdec t ht0
      have hsqrt_eq : √(3 * t / c') = √(3 / c') * √t := by
        rw [show 3 * t / c' = (3 / c') * t by ring, Real.sqrt_mul (by positivity)]
      have hexp_eq : Real.exp (-4 * π * √(c' / 12 * t) - π * √(3 * t / c')) *
          Real.exp (4 * π * √(c' / 12 * t)) = Real.exp (-(π * √(3 / c')) * √t) := by
        rw [← Real.exp_add, hsqrt_eq]
        congr 1; ring
      have hrp : (1 + 2 * t) ^ (-6 : ℝ) ≤ t ^ (-2 : ℝ) := by
        have h1t : 1 ≤ 1 + 2 * t := by linarith
        have ht_rpow : t ^ (2 : ℝ) ≤ (1 + 2 * t) ^ (6 : ℝ) := by
          have h2 : t ^ (2 : ℝ) ≤ (1 + 2 * t) ^ (2 : ℝ) :=
            Real.rpow_le_rpow ht0 (by linarith) (by norm_num)
          have h6 : (1 + 2 * t) ^ (2 : ℝ) ≤ (1 + 2 * t) ^ (6 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le h1t (by norm_num)
          exact h2.trans h6
        have h1 : (1 + 2 * t) ^ (-6 : ℝ) = ((1 + 2 * t) ^ (6 : ℝ))⁻¹ := by
          rw [← Real.rpow_neg (by linarith)]
        have h2 : t ^ (-2 : ℝ) = (t ^ (2 : ℝ))⁻¹ := by
          rw [← Real.rpow_neg ht0]
        rw [h1, h2]
        exact inv_anti₀ (Real.rpow_pos_of_pos (by linarith) 2) ht_rpow
      have hbd1 : |f t| ≤ C₁ * (C_g * Real.exp (-(π * √(3 / c')) * √t)) := by
        dsimp [f]
        rw [abs_mul, abs_of_nonneg hV_nn]
        calc |g t| * virasoroProblem.cardyV (c' / 12) t
            ≤ (C_g * Real.exp (-4 * π * √(c' / 12 * t) - π * √(3 * t / c'))) *
                (C₁ * Real.exp (4 * π * √(c' / 12 * t))) :=
              mul_le_mul hg_le hV_le hV_nn (by positivity)
          _ = C₁ * (C_g * (Real.exp (-4 * π * √(c' / 12 * t) - π * √(3 * t / c')) *
                Real.exp (4 * π * √(c' / 12 * t)))) := by ring
          _ = C₁ * (C_g * Real.exp (-(π * √(3 / c')) * √t)) := by rw [hexp_eq]
      rw [Real.norm_eq_abs]
      calc |f t| ≤ C₁ * (C_g * Real.exp (-(π * √(3 / c')) * √t)) := hbd1
        _ ≤ C₁ * (C_g * (C_δ * (1 + 2 * t) ^ (-6 : ℝ))) := by
            gcongr
            simpa [neg_mul] using hδ_bd t ht0
        _ ≤ C₁ * (C_g * (C_δ * t ^ (-2 : ℝ))) := by gcongr
        _ = C₁ * ((C_g * C_δ) * t ^ (-2 : ℝ)) := by ring
  rw [← Ioc_union_Ioi_eq_Ioi (a := (0 : ℝ)) (b := (1 : ℝ)) zero_le_one]
  exact hloc.union htail

private lemma psiAiry_virasoro_eq_w5_ratio {c' : ℝ} (hc' : 0 < c') (g : ℝ → ℝ) {u : ℝ}
    (hu : u < uEnd c') :
    psiScale virasoroProblem c' * psiAiry virasoroProblem c' g u =
      (qProb spinMomentW5Prob * virasoroProblem.cardyV (c' / 12) (tAiry c' u) /
          kernelK 5 (c' / 12) (tAiry c' u)) *
        (psiScale spinMomentW5Prob c' * psiAiry spinMomentW5Prob c' g u) := by
  have ht_pos : 0 < tAiry c' u := tAiry_pos_of_lt hc' hu
  have hK5_pos : 0 < kernelK 5 (c' / 12) (tAiry c' u) := by
    rw [← spinMomentW5Prob_cardyV]
    exact spinMomentW5Prob.cardyV_pos (by unfold FixedWeightProblem.totalShift spinMomentW5Prob; norm_num; positivity) ht_pos
  have hq5_pos : 0 < qProb spinMomentW5Prob := qProb_pos spinMomentW5Prob
  have hFK1 := FKc_pos (qProb_pos virasoroProblem) 1 hc'
  have hFK5 := FKc_pos hq5_pos 1 hc'
  have hCSt := CStar_pos
  unfold psiScale psiAiry
  rw [spinMomentW5Prob_cardyV, qProb_virasoro, FKc_q_eq (qProb spinMomentW5Prob) 1 c']
  have hK5_ne := hK5_pos.ne'
  have hq5_ne := hq5_pos.ne'
  have hFK1_ne := FKc_pos zero_lt_one 1 hc' |>.ne'
  have hCSt_ne := hCSt.ne'
  field_simp

private lemma tAiry_le_of_u_le_uAiry {c' u t : ℝ} (hc' : 0 < c') (ht : 0 ≤ t)
    (hu : u ≤ uAiry c' t) : t ≤ tAiry c' u := by
  have hsl : 0 < slopeAiry c' := slopeAiry_pos hc'
  have hba : √(3 * t / c') ≤ bAiry c' u := by
    calc √(3 * t / c') = bAiry c' (uAiry c' t) := (bAiry_uAiry hc' t).symm
      _ = max (xiStar - uAiry c' t * slopeAiry c') 0 := rfl
      _ ≤ max (xiStar - u * slopeAiry c') 0 := by gcongr
      _ = bAiry c' u := rfl
  have hsq : 3 * t / c' ≤ bAiry c' u ^ 2 := by
    have h0 : 0 ≤ √(3 * t / c') := Real.sqrt_nonneg _
    have h1 := mul_self_le_mul_self h0 hba
    rw [Real.mul_self_sqrt (by positivity), ← sq] at h1
    exact h1
  unfold tAiry
  calc t = c' / 3 * (3 * t / c') := by field_simp [hc'.ne']
    _ ≤ c' / 3 * bAiry c' u ^ 2 := by gcongr

/-! ### `DesignTest` and `DesignPropertyP` for `spinMomentVStar⁻¹ • spinMomentSpectralMeasure` -/

open Classical in
private noncomputable def spinMoment_designTest_of_sig
    (N : ℕ) (hN : 1 ≤ N) {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 4) (σs : ℕ → ℝ)
    (D : Window) (hW : D.W = sigWinW N η σs) (hUF : D.uF = -(kappaAiry * σs 1))
    (cSeq τSeq BSeq : ℕ → ℝ) (hc : Tendsto cSeq atTop atTop) (hc25 : ∀ j, 25 ≤ cSeq j)
    (hτ : ∀ j, 0 < τSeq j) (hB : ∀ j, 0 ≤ BSeq j)
    (hGap : GapCondition (fun j => cSeq j - 1) τSeq)
    (meas : ∀ j, SpinCrossingMeasureOn ((cSeq j - 1) / 12)
      (spinConeB (BSeq j) ∩ {p : ℝ × ℝ | τSeq j ≤ p.1 + p.2})) :
    DesignTest (fun j => ENNReal.ofReal spinMomentVStar⁻¹ •
      spinMomentSpectralMeasure (cSeq j - 1) (meas j).ν) D := by
  let c' : ℕ → ℝ := fun j => cSeq j - 1
  have hc' : Tendsto c' atTop atTop := hc.atTop_add tendsto_const_nhds
  let μ : ℕ → Measure ℝ := fun j =>
    ENNReal.ofReal spinMomentVStar⁻¹ • spinMomentSpectralMeasure (c' j) (meas j).ν
  have hv_pos : 0 < spinMomentVStar := spinMomentVStar_pos
  let d5 := (rpParams 4).bumpData
  let E5 := bumpEventual spinMomentW5Prob N hN hη0 hη1 σs D hW hUF
  have hE5_g : E5.g = bumpG spinMomentW5Prob d5 N η σs := rfl
  have hE5_scale : E5.scale = psiScale spinMomentW5Prob := rfl
  have hgap_top : ∀ᶠ j in atTop, uAiry (c' j) (τSeq j) ≤ airyZero 1 + 1 :=
    eventually_uAiry_le_of_gap hc' hGap 1 one_pos
  have hev_good : ∀ᶠ j in atTop,
      0 < c' j ∧ 0 < E5.scale (c' j) ∧ TestClass spinMomentW5Prob (c' j / 12) (E5.g (c' j)) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t →
        |E5.g (c' j) t| ≤ C * Real.exp (-4 * π * √(c' j / 12 * t) - π * √(3 * t / c' j))) ∧
      0 ≤ E5.tf (c' j) + 1 ∧ (∀ t : ℝ, E5.tf (c' j) + 1 ≤ t → 0 ≤ E5.g (c' j) t) ∧
      uAiry (c' j) (τSeq j) ≤ airyZero 1 + 1 ∧
      Integrable (fun u => psiScale virasoroProblem (c' j) *
        psiAiry virasoroProblem (c' j) (E5.g (c' j)) u) (spinMomentSpectralMeasure (c' j) (meas j).ν) := by
    have hpair1 := spinMoment_window_pair_limsup_le N hN hη0 hη1 σs D hW cSeq τSeq BSeq
      hc hc25 hτ hB hGap meas (ε := 1) one_pos
    filter_upwards [hc'.eventually E5.good, hgap_top, hpair1] with j hj1 hj2 hj3
    exact ⟨hj1.1, hj1.2.1, hj1.2.2.1, hj1.2.2.2.1, hj1.2.2.2.2.1, hj1.2.2.2.2.2, hj2, hj3.1⟩
  let J₀ : ℕ := Classical.choose (eventually_atTop.mp hev_good)
  have hJ₀ := Classical.choose_spec (eventually_atTop.mp hev_good)
  let θ : ℕ → ℝ := fun j => if j < J₀ then D.uF else uAiry (c' j) (E5.tf (c' j) + 1)
  let x₀ : ℕ → ℝ := fun j => max (airyZero 1 + 1) (θ j) + j + 2
  let Ψ₀ : ℕ → ℝ → ℝ := fun j u =>
    psiScale virasoroProblem (c' j) * psiAiry virasoroProblem (c' j) (E5.g (c' j)) u
  let scaleBump : ℕ → ℝ := fun j => (∫ u, Ψ₀ j u ∂μ j) - ∫ u, Ψ₀ j u
  let Ψ : ℕ → ℝ → ℝ := fun j u =>
    if j < J₀ then 0 else Ψ₀ j u + scaleBump j * tentFn (u - x₀ j)
  have hx₀_ge_gap : ∀ j, J₀ ≤ j → uAiry (c' j) (τSeq j) + 1 ≤ x₀ j := fun j hj => by
    have hgap_j := (hJ₀ j hj).2.2.2.2.2.2.1
    dsimp [x₀]
    linarith [le_max_left (airyZero 1 + 1) (θ j), show (0 : ℝ) ≤ j from Nat.cast_nonneg j]
  have hx₀_ge_theta : ∀ j, θ j + 1 ≤ x₀ j := fun j => by
    dsimp [x₀]
    linarith [le_max_right (airyZero 1 + 1) (θ j), show (0 : ℝ) ≤ j from Nat.cast_nonneg j]
  have hΨ₀_int_mu : ∀ j, J₀ ≤ j → Integrable (Ψ₀ j) (μ j) := fun j hj => by
    have hint := (hJ₀ j hj).2.2.2.2.2.2.2
    exact hint.smul_measure ENNReal.ofReal_lt_top.ne
  have hΨ₀_int_vol : ∀ j, J₀ ≤ j → Integrable (Ψ₀ j) := fun j hj => by
    obtain ⟨hc'0, -, htc, ⟨C_g, hCg0, hdec⟩, -, -, -, -⟩ := hJ₀ j hj
    have ha_vir : virasoroProblem.totalShift ≤ c' j / 12 := by
      rw [virasoroProblem_totalShift]; dsimp [c']; linarith [hc25 j]
    exact (virasoro_bump_integrable hc'0 ha_vir hCg0 htc.cont hdec).const_mul _
  have hμ_supp : ∀ j, (μ j) (Ioi (uAiry (c' j) (τSeq j))) = 0 := fun j => by
    have hc'0 : 0 < c' j := by dsimp [c']; linarith [hc25 j]
    have ha_vir : virasoroProblem.totalShift ≤ c' j / 12 := by
      rw [virasoroProblem_totalShift]; dsimp [c']; linarith [hc25 j]
    have hs := spinMomentSpectralMeasure_supp hc'0 (hτ j)
      (fun _ (hp : _ ∈ spinConeB (BSeq j) ∩ {p | τSeq j ≤ p.1 + p.2}) => hp.2) (meas j)
    simp [μ, hs]
  have htent_ae_zero : ∀ j, J₀ ≤ j →
      (fun u => scaleBump j * tentFn (u - x₀ j)) =ᵐ[μ j] 0 := fun j hj => by
    have h0 := hμ_supp j
    rw [Filter.EventuallyEq, ae_iff]
    refine measure_mono_null (fun u hu => ?_) h0
    rw [Set.mem_Ioi]
    by_contra hle
    push Not at hle
    apply hu
    have hdiff : u - x₀ j ≤ -1 := by linarith [hx₀_ge_gap j hj]
    simp [tentFn_eq_zero_of_le_neg_one hdiff]
  refine
    { Ψ := Ψ
      θ := θ
      continuous := fun j => by
        dsimp [Ψ]
        split_ifs with hlt
        · exact continuous_zero
        · have hj : J₀ ≤ j := not_lt.mp hlt
          have hc'0 : 0 < c' j := (hJ₀ j hj).1
          have hcont_g : ContinuousOn (E5.g (c' j)) (Ici 0) := (hJ₀ j hj).2.2.1.cont
          have hΨ0_cont : Continuous (Ψ₀ j) :=
            continuous_const.mul (continuous_psiAiry hc'0 hcont_g)
          exact hΨ0_cont.add (continuous_const.mul (continuous_tentFn.comp (continuous_id.sub continuous_const)))
      integrable_mu := fun j => by
        dsimp [Ψ]
        split_ifs with hlt
        · exact integrable_zero _ _ _
        · have hj : J₀ ≤ j := not_lt.mp hlt
          have h1 : Integrable (fun u => Ψ₀ j u + scaleBump j * tentFn (u - x₀ j)) (μ j) := by
            have hadd : (fun u => Ψ₀ j u + scaleBump j * tentFn (u - x₀ j)) =ᵐ[μ j] Ψ₀ j := by
              filter_upwards [htent_ae_zero j hj] with u hu
              simp [hu]
            exact (hΨ₀_int_mu j hj).congr hadd.symm
          exact h1
      integrable_vol := fun j => by
        dsimp [Ψ]
        split_ifs with hlt
        · exact integrable_zero _ _ _
        · have hj : J₀ ≤ j := not_lt.mp hlt
          have htent_shift : Integrable (fun u => scaleBump j * tentFn (u - x₀ j)) :=
            (integrable_tentFn.comp_sub_right (x₀ j)).const_mul _
          exact (hΨ₀_int_vol j hj).add htent_shift
      crossing := fun j => by
        dsimp [Ψ]
        split_ifs with hlt
        · simp
        · have hj : J₀ ≤ j := not_lt.mp hlt
          have htent_shift : Integrable (fun u => scaleBump j * tentFn (u - x₀ j)) :=
            (integrable_tentFn.comp_sub_right (x₀ j)).const_mul _
          have hL : ∫ u, (Ψ₀ j u + scaleBump j * tentFn (u - x₀ j)) ∂μ j = ∫ u, Ψ₀ j u ∂μ j := by
            refine integral_congr_ae ?_
            filter_upwards [htent_ae_zero j hj] with u hu
            simp [hu]
          have h_sc : ∫ u, scaleBump j * tentFn (u - x₀ j) = scaleBump j := by
            rw [integral_const_mul, MeasureTheory.integral_sub_right_eq_self tentFn (x₀ j),
              integral_tentFn, mul_one]
          have hR : ∫ u, (Ψ₀ j u + scaleBump j * tentFn (u - x₀ j)) =
              (∫ u, Ψ₀ j u) + scaleBump j := by
            rw [integral_add (hΨ₀_int_vol j hj) htent_shift, h_sc]
          rw [hL, hR]
          dsimp [scaleBump]
          ring
      nonneg := fun j u hu => by
        dsimp [Ψ]
        split_ifs with hlt
        · exact le_rfl
        · have hj : J₀ ≤ j := not_lt.mp hlt
          have htent0 : tentFn (u - x₀ j) = 0 :=
            tentFn_eq_zero_of_le_neg_one (by linarith [hx₀_ge_theta j])
          rw [htent0, mul_zero, add_zero]
          obtain ⟨hc'0, -, -, -, htf0, hgnn, -, -⟩ := hJ₀ j hj
          dsimp [Ψ₀]
          by_cases huend : u < uEnd (c' j)
          · have htu : E5.tf (c' j) + 1 ≤ tAiry (c' j) u := by
              have hu' : u ≤ uAiry (c' j) (E5.tf (c' j) + 1) := by
                simpa [θ, hlt] using hu
              exact tAiry_le_of_u_le_uAiry hc'0 htf0 hu'
            have hg_nn : 0 ≤ E5.g (c' j) (tAiry (c' j) u) := hgnn _ htu
            have ha_vir : virasoroProblem.totalShift ≤ c' j / 12 := by
              rw [virasoroProblem_totalShift]; dsimp [c']; linarith [hc25 j]
            have hV_nn := virasoroProblem.cardyV_nonneg ha_vir (tAiry_nonneg hc'0 u)
            have hj_nn : 0 ≤ jAiry (c' j) (tAiry (c' j) u) :=
              (jAiry_pos hc'0 (tAiry_pos_of_lt hc'0 huend)).le
            have hps_nn : 0 ≤ psiScale virasoroProblem (c' j) := by
              unfold psiScale
              have := CStar_pos; have := FKc_pos (qProb_pos virasoroProblem) 1 hc'0; positivity
            unfold psiAiry
            exact mul_nonneg hps_nn (mul_nonneg (mul_nonneg hg_nn hV_nn) hj_nn)
          · push Not at huend
            rw [psiAiry_eq_zero_of_le hc'0 huend, mul_zero]
      theta_tendsto := by
        refine (E5.theta.comp hc').congr' ?_
        filter_upwards [eventually_ge_atTop J₀] with j hj
        simp [θ, not_lt.mpr hj]
      window_limit := by
        rw [tendstoLocallyUniformly_iff_forall_isCompact]
        intro K hKc
        obtain ⟨R, hR0, hKR⟩ : ∃ R : ℝ, 0 ≤ R ∧ K ⊆ Icc (-R) R := by
          by_cases hne : K.Nonempty
          · obtain ⟨a, ha⟩ := hKc.bddAbove
            obtain ⟨b, hb⟩ := hKc.bddBelow
            refine ⟨max (|a|) (|b|) + 1, by positivity, fun x hx => ⟨?_, ?_⟩⟩
            · linarith [hb hx, le_abs_self (-b), neg_abs_le b, le_max_right (|a|) (|b|)]
            · linarith [ha hx, le_abs_self a, le_max_left (|a|) (|b|)]
          · rw [Set.not_nonempty_iff_eq_empty] at hne
            subst hne
            exact ⟨0, le_rfl, empty_subset _⟩
        rw [Metric.tendstoUniformlyOn_iff]
        intro ε hε
        have hW_bd : ∃ M : ℝ, 0 < M ∧ ∀ u ∈ Icc (-R) R, |D.W u| ≤ M := by
          obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn D.continuous.continuousOn
          refine ⟨max M 1, by positivity, fun u hu => ?_⟩
          simpa [Real.norm_eq_abs] using (hM u hu).trans (le_max_left M 1)
        obtain ⟨M, hM0, hWM⟩ := hW_bd
        set δ₁ := min 1 (ε / (2 * (M + 1)))
        have hδ₁ : 0 < δ₁ := by positivity
        set δ₂ := ε / (2 * (M + 1))
        have hδ₂ : 0 < δ₂ := by positivity
        have hw5_unif := (E5.window R hR0 δ₂ hδ₂).mono fun c hc u hu => hc u hu
        obtain ⟨ρw, hρw, hrat_unif⟩ := virasoro_w5_cardy_ratio_tendsto (half_pos xiStar_pos)
          (by linarith [xiStar_pos] : xiStar / 2 ≤ xiStar + 1 / 2) δ₁ hδ₁
        have hslope_rw : Tendsto slopeAiry atTop (nhds 0) := by
          have heq : slopeAiry = fun c => c ^ (-(2 / 3 : ℝ)) / betaTip := by
            ext c; unfold slopeAiry epsAiry; rfl
          rw [heq]
          simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).div_const betaTip
        have hR_sl : ∀ᶠ c' in atTop, R * slopeAiry c' ≤ ρw := by
          have ht : Tendsto (fun c' => R * slopeAiry c') atTop (nhds 0) := by
            simpa only [mul_zero] using hslope_rw.const_mul R
          exact ht.eventually_le_const hρw
        have hbA := bAiry_eq_of_Icc hR0
        have hx₀_top : Tendsto x₀ atTop atTop := by
          have : Tendsto (fun j : ℕ => (airyZero 1 + 1) + (j : ℝ) + 2) atTop atTop :=
            ((tendsto_const_nhds (x := airyZero 1 + 1)).add_atTop
              (tendsto_natCast_atTop_atTop (R := ℝ))).atTop_add tendsto_const_nhds
          refine tendsto_atTop_mono (fun j => ?_) this
          dsimp [x₀]
          linarith [le_max_left (airyZero 1 + 1) (θ j)]
        filter_upwards [eventually_ge_atTop J₀, hc'.eventually hw5_unif, hc'.eventually hrat_unif,
          hc'.eventually hR_sl, hc'.eventually hbA, hx₀_top.eventually_ge_atTop (R + 1)] with
            j hj h5j hratj hRslj hbAj hx0j u huK
        have huR : u ∈ Icc (-R) R := hKR huK
        have htent0 : tentFn (u - x₀ j) = 0 :=
          tentFn_eq_zero_of_le_neg_one (by linarith [huR.2, hx0j])
        have hΨ_eq : Ψ j u = Ψ₀ j u := by
          dsimp [Ψ]
          rw [ite_eq_right_iff.mpr fun h => absurd h (not_lt.mpr hj), htent0, mul_zero, add_zero]
        rw [Real.dist_eq, abs_sub_comm, hΨ_eq]
        have hc'0 : 0 < c' j := (hJ₀ j hj).1
        obtain ⟨hb_eq, -, -⟩ := hbAj u huR
        have huend : u < uEnd (c' j) := by
          rw [lt_uEnd_iff hc'0]
          have : 0 < bAiry (c' j) u := by linarith [xiStar_pos, (hbAj u huR).2.1]
          linarith [show bAiry (c' j) u = xiStar - u * slopeAiry (c' j) from hb_eq]
        have hb_rho : |bAiry (c' j) u - xiStar| ≤ ρw := by
          rw [hb_eq, show xiStar - u * slopeAiry (c' j) - xiStar = -(u * slopeAiry (c' j)) by ring,
            abs_neg, abs_mul, abs_of_pos (slopeAiry_pos hc'0)]
          exact (mul_le_mul_of_nonneg_right (abs_le.mpr ⟨huR.1, huR.2⟩) (slopeAiry_pos hc'0).le).trans hRslj
        have hratio_bd : |qProb spinMomentW5Prob * virasoroProblem.cardyV (c' j / 12) (tAiry (c' j) u) /
            kernelK 5 (c' j / 12) (tAiry (c' j) u) - 1| ≤ δ₁ := by
          have ht_eq : tAiry (c' j) u = c' j * (bAiry (c' j) u) ^ 2 / 3 := by
            unfold tAiry; ring
          rw [ht_eq]
          exact hratj (bAiry (c' j) u) hb_rho
        have h5_bd : |E5.scale (c' j) * psiAiry spinMomentW5Prob (c' j) (E5.g (c' j)) u - D.W u| ≤ δ₂ :=
          h5j u huR
        have h5_abs : |E5.scale (c' j) * psiAiry spinMomentW5Prob (c' j) (E5.g (c' j)) u| ≤
            M + δ₂ := by
          have htri := abs_sub_le (E5.scale (c' j) * psiAiry spinMomentW5Prob (c' j) (E5.g (c' j)) u)
            (D.W u) 0
          rw [sub_zero, sub_zero] at htri
          linarith [hWM u huR]
        set q := qProb spinMomentW5Prob * virasoroProblem.cardyV (c' j / 12) (tAiry (c' j) u) /
            kernelK 5 (c' j / 12) (tAiry (c' j) u)
        set p := E5.scale (c' j) * psiAiry spinMomentW5Prob (c' j) (E5.g (c' j)) u
        have hΨ0_eq : Ψ₀ j u = q * p := by
          dsimp [Ψ₀, q, p]
          rw [hE5_scale]
          exact psiAiry_virasoro_eq_w5_ratio hc'0 (E5.g (c' j)) huend
        rw [hΨ0_eq]
        have hsplit : q * p - D.W u = (q - 1) * p + (p - D.W u) := by ring
        rw [hsplit]
        have hq_sub : |q - 1| ≤ δ₁ := hratio_bd
        have hδ1_le1 : δ₁ ≤ 1 := min_le_left _ _
        have hδ1_le_eps : δ₁ ≤ ε / (2 * (M + 1)) := min_le_right _ _
        have hp_le : |p| ≤ M + δ₂ := h5_abs
        calc |(q - 1) * p + (p - D.W u)| ≤ |(q - 1) * p| + |p - D.W u| := abs_add_le _ _
          _ = |q - 1| * |p| + |p - D.W u| := by rw [abs_mul]
          _ ≤ |q - 1| * (M + δ₂) + δ₂ := add_le_add (mul_le_mul_of_nonneg_left hp_le (abs_nonneg _)) h5_bd
          _ ≤ δ₁ * M + δ₁ * δ₂ + δ₂ := by
              nlinarith [mul_le_mul_of_nonneg_right hq_sub (by positivity : 0 ≤ M + δ₂)]
          _ ≤ (ε / (2 * (M + 1))) * M + 1 * δ₂ + δ₂ := by
              gcongr
          _ = ε * ((M + 2) / (2 * (M + 1))) := by
              have hM1 : M + 1 ≠ 0 := by positivity
              dsimp [δ₂]; field_simp; ring
          _ < ε := by
              have h_lt1 : (M + 2) / (2 * (M + 1)) < 1 := by
                rw [div_lt_one (by positivity)]; linarith
              nlinarith
      limsup_le := fun ε hε => by
        have hpair := spinMoment_window_pair_limsup_le N hN hη0 hη1 σs D hW cSeq τSeq BSeq
          hc hc25 hτ hB hGap meas (ε := ε * spinMomentVStar) (by positivity)
        filter_upwards [eventually_ge_atTop J₀, hpair] with j hj ⟨_, hj_le⟩
        have hL : ∫ u, Ψ j u = ∫ u, Ψ₀ j u ∂μ j := by
          have hΨ_j : Ψ j = fun u => Ψ₀ j u + scaleBump j * tentFn (u - x₀ j) :=
            funext fun u => ite_eq_right_iff.mpr fun h => absurd h (not_lt.mpr hj)
          rw [hΨ_j]
          have htent_shift : Integrable (fun u => scaleBump j * tentFn (u - x₀ j)) :=
            (integrable_tentFn.comp_sub_right (x₀ j)).const_mul _
          have h_sc : ∫ u, scaleBump j * tentFn (u - x₀ j) = scaleBump j := by
            rw [integral_const_mul, MeasureTheory.integral_sub_right_eq_self tentFn (x₀ j),
              integral_tentFn, mul_one]
          rw [integral_add (hΨ₀_int_vol j hj) htent_shift, h_sc]
          dsimp [scaleBump]; ring
        rw [hL]
        have hμ_eq : ∫ u, Ψ₀ j u ∂μ j =
            spinMomentVStar⁻¹ * ∫ u, Ψ₀ j u ∂(spinMomentSpectralMeasure (c' j) (meas j).ν) := by
          dsimp [μ]
          rw [integral_smul_measure, ENNReal.toReal_ofReal (inv_nonneg.mpr hv_pos.le), smul_eq_mul]
        rw [hμ_eq]
        have hj_le' : ∫ u, Ψ₀ j u ∂(spinMomentSpectralMeasure (c' j) (meas j).ν) ≤
            spinMomentVStar * D.V + ε * spinMomentVStar := hj_le
        calc spinMomentVStar⁻¹ * ∫ u, Ψ₀ j u ∂(spinMomentSpectralMeasure (c' j) (meas j).ν)
            ≤ spinMomentVStar⁻¹ * (spinMomentVStar * D.V + ε * spinMomentVStar) :=
              mul_le_mul_of_nonneg_left hj_le' (inv_nonneg.mpr hv_pos.le)
          _ = D.V + ε := by field_simp [hv_pos.ne'] }

private lemma spinMoment_designPropertyP
    (cSeq τSeq BSeq : ℕ → ℝ) (hc : Tendsto cSeq atTop atTop) (hc25 : ∀ j, 25 ≤ cSeq j)
    (hτ : ∀ j, 0 < τSeq j) (hB : ∀ j, 0 ≤ BSeq j)
    (hGap : GapCondition (fun j => cSeq j - 1) τSeq)
    (meas : ∀ j, SpinCrossingMeasureOn ((cSeq j - 1) / 12)
      (spinConeB (BSeq j) ∩ {p : ℝ × ℝ | τSeq j ≤ p.1 + p.2})) :
    DesignPropertyP (fun j => ENNReal.ofReal spinMomentVStar⁻¹ •
      spinMomentSpectralMeasure (cSeq j - 1) (meas j).ν) (designClass ∪ displacedClassX) := by
  intro D hD
  rcases hD with hD | hD
  · obtain ⟨N, η, d, hη0, hN, hη1, rfl⟩ := hD
    exact ⟨spinMoment_designTest_of_sig N hN hη0 hη1 (designSigma1 d) (designWin N hη0 d)
      (designWin_W_eq_sig N hη0 d) (designWin_uF_eq_sig N hη0 d)
      cSeq τSeq BSeq hc hc25 hτ hB hGap meas⟩
  · obtain ⟨N, η, e, d, hη0, hH, hN, hη1, he, rfl⟩ := hD
    have hW : (profWin (dispSite N e) (designWidthU N η) hH
        (fun _ hk => designWidthU_ne_zero N hη0 hk) d).W = sigWinW N η (dispSigma d e) := by
      funext u
      rw [profWin_W]
      show (Upper.Ramped.profW (dispSite N e) (designWidthU N η) d (u : ℂ)).re =
        (sigWindowW N η (dispSigma d e) (u : ℂ)).re
      rw [sigWindowW_dispSite N η d e he]
    have hUF : (profWin (dispSite N e) (designWidthU N η) hH
        (fun _ hk => designWidthU_ne_zero N hη0 hk) d).uF = -(kappaAiry * dispSigma d e 1) := by
      rw [profWin_uF, dispSigma_one]
    exact ⟨spinMoment_designTest_of_sig N hN hη0 hη1 (dispSigma d e) _ hW hUF
      cSeq τSeq BSeq hc hc25 hτ hB hGap meas⟩

/-! ### `sd:spinmoment`: vague limit and cluster second-moment ratio -/

/-- **`sd:spinmoment` (vague limit)** (`spinning_airy_moment.tex`, Theorem SD-M2, eq.
`sd:spinmoment-limit`): for every admissible sequence `(c_j, τ_j, B_j, meas_j)` with gap
`GapCondition (c_j - 1) τ_j`, the normalised spin-moment spectral measures
`spinMomentSpectralMeasure (c_j - 1) (meas j).ν` tend vaguely on `ℝ` to
`spinMomentVStar • airyMeasure`, with `spinMomentVStar = 2 * xiStar ^ 3 / (3 * π)`.
Neither spin integrality, attainment, nor a uniform bound on `B_j` is required. -/
theorem spinMoment_vagueLimit
    (cSeq τSeq BSeq : ℕ → ℝ) (hc : Tendsto cSeq atTop atTop) (hc25 : ∀ j, 25 ≤ cSeq j)
    (hτ : ∀ j, 0 < τSeq j) (hB : ∀ j, 0 ≤ BSeq j)
    (hGap : GapCondition (fun j => cSeq j - 1) τSeq)
    (meas : ∀ j, SpinCrossingMeasureOn ((cSeq j - 1) / 12)
      (spinConeB (BSeq j) ∩ {p : ℝ × ℝ | τSeq j ≤ p.1 + p.2})) :
    IsVagueLimit atTop
      (fun j => spinMomentSpectralMeasure (cSeq j - 1) (meas j).ν)
      (ENNReal.ofReal spinMomentVStar • airyMeasure) := by
  let c' : ℕ → ℝ := fun j => cSeq j - 1
  have hc' : Tendsto c' atTop atTop := hc.atTop_add tendsto_const_nhds
  let μ_raw : ℕ → Measure ℝ := fun j => spinMomentSpectralMeasure (c' j) (meas j).ν
  let μ : ℕ → Measure ℝ := fun j => ENNReal.ofReal spinMomentVStar⁻¹ • μ_raw j
  have : ∀ j, IsLocallyFiniteMeasure (μ_raw j) := fun j => by
    have hc'24 : 24 ≤ c' j := by dsimp [c']; linarith [hc25 j]
    have ha2 : 2 ≤ c' j / 12 := by linarith
    exact spinMomentSpectralMeasure_isLocallyFinite hc'24 ha2 (hB j) (hτ j) Subset.rfl (meas j)
  have : ∀ j, IsLocallyFiniteMeasure (μ j) := fun j =>
    ⟨fun x => ⟨Icc (x - 1) (x + 1), Icc_mem_nhds (by linarith) (by linarith), by
      have : IsLocallyFiniteMeasure (μ_raw j) := ‹∀ j, IsLocallyFiniteMeasure (μ_raw j)› j
      dsimp [μ]
      simpa using ENNReal.mul_lt_top ENNReal.ofReal_lt_top isCompact_Icc.measure_lt_top⟩⟩
  have hsupp : ∀ j, μ j (Ioi (uAiry (c' j) (τSeq j))) = 0 := fun j => by
    have hc'0 : 0 < c' j := by dsimp [c']; linarith [hc25 j]
    have hs := spinMomentSpectralMeasure_supp hc'0 (hτ j)
      (fun _ (hp : _ ∈ spinConeB (BSeq j) ∩ {p | τSeq j ≤ p.1 + p.2}) => hp.2) (meas j)
    simp [μ, μ_raw, hs]
  let S : SpectralData := SpectralData.ofGap hc' hGap μ hsupp
  have hP := spinMoment_designPropertyP cSeq τSeq BSeq hc hc25 hτ hB hGap meas
  have hSig := theorem_Sigma S hP
    (Upper.Assembly.SameSiteFamily.mono subset_union_left sameSiteFamily_designClass_exists.some)
    (Upper.Assembly.DisplacedFamily.mono subset_union_right
      (displacedFamily_exists displacedClass_subset).some)
    farFamily
  have hVag := hSig.2.2.2.1
  intro φ hφc hφcs
  have hv_pos : 0 < spinMomentVStar := spinMomentVStar_pos
  have hlim : Tendsto (fun j => spinMomentVStar * ∫ u, φ u ∂μ j) atTop
      (𝓝 (spinMomentVStar * ∫ u, φ u ∂airyMeasure)) :=
    (hVag φ hφc hφcs).const_mul spinMomentVStar
  refine hlim.congr' (Eventually.of_forall fun j => ?_) |>.trans_eq ?_
  · dsimp [μ]
    rw [integral_smul_measure, ENNReal.toReal_ofReal (inv_nonneg.mpr hv_pos.le), smul_eq_mul,
      ← mul_assoc, mul_inv_cancel₀ hv_pos.ne', one_mul]
  · rw [integral_smul_measure, ENNReal.toReal_ofReal hv_pos.le, smul_eq_mul]

/-- info: 'FormalResearch.ModularBootstrap.Spin.spinMoment_vagueLimit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms spinMoment_vagueLimit

private lemma airyMeasure_singleton_mul {c : ℝ} (hc : 0 ≤ c) {I : Set ℝ} {k : ℕ}
    (hk : airyNode k ∈ interior I) (hiso : closure I ∩ Set.range airyNode ⊆ {airyNode k}) :
    ((ENNReal.ofReal c • airyMeasure) (closure I)).toReal = c * airyNodeWeight k ∧
      ((ENNReal.ofReal c • airyMeasure) {airyNode k}).toReal = c * airyNodeWeight k := by
  have hI_node : closure I ∩ Set.range airyNode = {airyNode k} :=
    le_antisymm hiso (Set.singleton_subset_iff.mpr ⟨subset_closure (interior_subset hk), ⟨k, rfl⟩⟩)
  have hm_eq : airyMeasure (closure I) = ENNReal.ofReal (airyNodeWeight k) := by
    have hsplit : closure I = (closure I ∩ Set.range airyNode) ∪ (closure I \ Set.range airyNode) := by
      ext u; simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_sdiff]; tauto
    rw [hsplit, measure_union (Set.disjoint_left.2 fun _ (hu1 : _ ∈ closure I ∩ Set.range airyNode)
        (hu2 : _ ∈ closure I \ Set.range airyNode) => hu2.2 hu1.2)
      (measurableSet_closure.diff measurableSet_range_airyNode)]
    have hnull : airyMeasure (closure I \ Set.range airyNode) = 0 :=
      measure_mono_null (fun _ h => h.2) airyMeasure_compl_range
    rw [hnull, add_zero, hI_node, airyMeasure_singleton]
  have hsingle : airyMeasure {airyNode k} = ENNReal.ofReal (airyNodeWeight k) :=
    airyMeasure_singleton k
  have hwnn : 0 ≤ airyNodeWeight k := (airyNodeWeight_pos k).le
  refine ⟨?_, ?_⟩
  · simp [hm_eq, ENNReal.toReal_mul, ENNReal.toReal_ofReal hc, ENNReal.toReal_ofReal hwnn]
  · simp [hsingle, ENNReal.toReal_mul, ENNReal.toReal_ofReal hc, ENNReal.toReal_ofReal hwnn]

private lemma tendsto_measure_isolating_lower
    {μ : ℕ → Measure ℝ} [∀ j, IsLocallyFiniteMeasure (μ j)]
    {ν : Measure ℝ} [IsLocallyFiniteMeasure ν] {L : ℝ}
    {I : Set ℝ} (hbd : Bornology.IsBounded I) {k : ℕ} (hk : airyNode k ∈ interior I)
    (hiso : closure I ∩ Set.range airyNode ⊆ {airyNode k})
    (hν_range : ν (Set.range airyNode)ᶜ = 0)
    (hsingle_val : (ν {airyNode k}).toReal = L)
    (hvag : IsVagueLimit atTop μ ν)
    {a : ℝ} (ha : a < L) :
    ∀ᶠ j in atTop, a < (μ j I).toReal := by
  have hcl_c : IsCompact (closure I) := hbd.isCompact_closure
  obtain ⟨r, hr0, hrI⟩ := Metric.isOpen_iff.mp isOpen_interior (airyNode k) hk
  let fm : ℝ → ℝ := fun u => max 0 (1 - |u - airyNode k| / r)
  have hfm_cont : Continuous fm :=
    continuous_const.max (continuous_const.sub
      ((continuous_abs.comp (continuous_id.sub continuous_const)).div_const r))
  have hfm_supp : HasCompactSupport fm := by
    refine HasCompactSupport.intro (isCompact_Icc (a := airyNode k - r) (b := airyNode k + r))
      fun u hu => ?_
    rw [max_eq_left_iff, sub_nonpos, one_le_div hr0]
    by_contra hlt
    push Not at hlt
    exact hu ⟨by linarith [(abs_lt.mp hlt).1], by linarith [(abs_lt.mp hlt).2]⟩
  have hfm_int_ν : ∫ u, fm u ∂ν = L := by
    have hae : fm =ᵐ[ν] Set.indicator {airyNode k} (fun _ => (1 : ℝ)) := by
      refine ae_iff.mpr (measure_mono_null (fun u hu => ?_) hν_range)
      exact (Set.mem_compl_iff _ u).2 fun hur => by
        apply hu
        by_cases huk : u = airyNode k
        · subst huk; simp [fm]
        · have hu_notin_cl : u ∉ closure I := fun hcl => huk (hiso ⟨hcl, hur⟩)
          have hu_notin_int : u ∉ interior I :=
            fun hint => hu_notin_cl (subset_closure (interior_subset hint))
          have hu_ball : ¬ dist u (airyNode k) < r := fun hlt => hu_notin_int (hrI hlt)
          rw [Real.dist_eq, not_lt] at hu_ball
          have h0 : fm u = 0 := by
            rw [max_eq_left_iff, sub_nonpos, one_le_div hr0]; exact hu_ball
          simp [h0, Set.indicator_of_notMem (Set.mem_singleton_iff.not.mpr huk)]
    rw [integral_congr_ae hae, integral_indicator (measurableSet_singleton _),
      setIntegral_const, smul_eq_mul, mul_one, Measure.real_def, hsingle_val]
  have hlim := hvag fm hfm_cont hfm_supp
  rw [hfm_int_ν] at hlim
  filter_upwards [hlim (Ioi_mem_nhds ha)] with j hj
  have hfin_int : μ j (interior I) < ∞ :=
    (measure_mono (interior_subset.trans subset_closure)).trans_lt hcl_c.measure_lt_top
  have hfinI : μ j I < ∞ := (measure_mono subset_closure).trans_lt hcl_c.measure_lt_top
  have hint_le : ∫ u, fm u ∂(μ j) ≤ (μ j (interior I)).toReal := by
    have hle_ind : ∀ u, fm u ≤ Set.indicator (interior I) (fun _ => (1 : ℝ)) u := fun u => by
      by_cases hu : u ∈ interior I
      · rw [Set.indicator_of_mem hu]
        exact max_le zero_le_one (by linarith [div_nonneg (abs_nonneg (u - airyNode k)) hr0.le])
      · have hu_ball : ¬ dist u (airyNode k) < r := fun hlt => hu (hrI hlt)
        rw [Real.dist_eq, not_lt] at hu_ball
        have h0 : fm u = 0 := by
          rw [max_eq_left_iff, sub_nonpos, one_le_div hr0]; exact hu_ball
        rw [h0, Set.indicator_of_notMem hu]
    have hfm_int_j : Integrable fm (μ j) := hfm_cont.integrable_of_hasCompactSupport hfm_supp
    have hind_int_j : Integrable (Set.indicator (interior I) (fun _ => (1 : ℝ))) (μ j) :=
      (integrable_indicator_iff isOpen_interior.measurableSet).mpr
        (integrableOn_const (C := (1 : ℝ)) hfin_int.ne)
    calc ∫ u, fm u ∂(μ j)
        ≤ ∫ u, Set.indicator (interior I) (fun _ => (1 : ℝ)) u ∂(μ j) :=
          integral_mono hfm_int_j hind_int_j hle_ind
      _ = (μ j (interior I)).toReal := by
          rw [integral_indicator isOpen_interior.measurableSet, setIntegral_const,
            smul_eq_mul, mul_one, Measure.real_def]
  have hmono : (μ j (interior I)).toReal ≤ (μ j I).toReal :=
    ENNReal.toReal_mono hfinI.ne (measure_mono interior_subset)
  have hj' : a < ∫ u, fm u ∂(μ j) := hj
  linarith only [hj', hint_le, hmono]

private lemma tendsto_measure_isolating_upper
    {μ : ℕ → Measure ℝ} [∀ j, IsLocallyFiniteMeasure (μ j)]
    {ν : Measure ℝ} [IsLocallyFiniteMeasure ν] {L : ℝ}
    {I : Set ℝ} (hbd : Bornology.IsBounded I)
    (hcl_val : (ν (closure I)).toReal = L)
    (hvag : IsVagueLimit atTop μ ν)
    {b : ℝ} (hb : L < b) :
    ∀ᶠ j in atTop, (μ j I).toReal < b := by
  have hcl_c : IsCompact (closure I) := hbd.isCompact_closure
  set ε := (b - L) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hε' : ENNReal.ofReal ε ≠ 0 := by simpa using hε
  obtain ⟨V, hCV, hVo, hV⟩ := hcl_c.exists_isOpen_lt_add (μ := ν) hε'
  have hVfin : ν V < ∞ := hV.trans (ENNReal.add_lt_top.2 ⟨hcl_c.measure_lt_top, ENNReal.ofReal_lt_top⟩)
  have hV_le : (ν V).toReal < L + ε := by
    have h1 := (ENNReal.toReal_lt_toReal hVfin.ne
      (ENNReal.add_ne_top.2 ⟨hcl_c.measure_lt_top.ne, ENNReal.ofReal_ne_top⟩)).2 hV
    rwa [ENNReal.toReal_add hcl_c.measure_lt_top.ne ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hε.le, hcl_val] at h1
  obtain ⟨fp, hfp1, hfp0, hfpc, hfp01⟩ := exists_continuous_one_zero_of_isCompact hcl_c
    hVo.isClosed_compl (disjoint_compl_right_iff_subset.mpr hCV)
  have hfp_int_ν : ∫ u, fp u ∂ν ≤ (ν V).toReal := by
    have hle_ind : ∀ u, fp u ≤ Set.indicator V (fun _ => (1 : ℝ)) u := fun u => by
      by_cases hu : u ∈ V
      · rw [Set.indicator_of_mem hu]; exact (hfp01 u).2
      · rw [Set.indicator_of_notMem hu, hfp0 hu]; rfl
    have hfp_int : Integrable fp ν := fp.continuous.integrable_of_hasCompactSupport hfpc
    have hind_int : Integrable (Set.indicator V (fun _ => (1 : ℝ))) ν :=
      (integrable_indicator_iff hVo.measurableSet).mpr
        (integrableOn_const (C := (1 : ℝ)) hVfin.ne)
    calc ∫ u, fp u ∂ν ≤ ∫ u, Set.indicator V (fun _ => (1 : ℝ)) u ∂ν :=
          integral_mono hfp_int hind_int hle_ind
      _ = (ν V).toReal := by
          rw [integral_indicator hVo.measurableSet, setIntegral_const, smul_eq_mul, mul_one,
            Measure.real_def]
  have hlim := hvag fp fp.continuous hfpc
  have hlt_b : ∫ u, fp u ∂ν < b := by
    linarith only [hb, hfp_int_ν, hV_le, show ε = (b - L) / 2 from rfl]
  filter_upwards [hlim (Iio_mem_nhds hlt_b)] with j hj
  have hcl_le : (μ j (closure I)).toReal ≤ ∫ u, fp u ∂(μ j) := by
    have hle_ind : ∀ u, Set.indicator (closure I) (fun _ => (1 : ℝ)) u ≤ fp u := fun u => by
      by_cases hu : u ∈ closure I
      · rw [Set.indicator_of_mem hu, hfp1 hu]; rfl
      · rw [Set.indicator_of_notMem hu]; exact (hfp01 u).1
    have hfp_int_j : Integrable fp (μ j) := fp.continuous.integrable_of_hasCompactSupport hfpc
    have hind_int_j : Integrable (Set.indicator (closure I) (fun _ => (1 : ℝ))) (μ j) :=
      (integrable_indicator_iff isClosed_closure.measurableSet).mpr
        (integrableOn_const (C := (1 : ℝ)) hcl_c.measure_lt_top.ne)
    calc (μ j (closure I)).toReal
        = ∫ u, Set.indicator (closure I) (fun _ => (1 : ℝ)) u ∂(μ j) := by
          rw [integral_indicator isClosed_closure.measurableSet, setIntegral_const,
            smul_eq_mul, mul_one, Measure.real_def]
      _ ≤ ∫ u, fp u ∂(μ j) := integral_mono hind_int_j hfp_int_j hle_ind
  have hfin_cl : μ j (closure I) < ∞ := hcl_c.measure_lt_top
  have hmono : (μ j I).toReal ≤ (μ j (closure I)).toReal :=
    ENNReal.toReal_mono hfin_cl.ne (measure_mono subset_closure)
  have hj' : ∫ u, fp u ∂(μ j) < b := hj
  linarith only [hj', hcl_le, hmono]

private lemma isLocallyFinite_smul_airyMeasure (c : ℝ) :
    IsLocallyFiniteMeasure (ENNReal.ofReal c • airyMeasure) :=
  ⟨fun x => ⟨Ioo (x - 1) (x + 1), Ioo_mem_nhds (by linarith) (by linarith), by
    have : IsLocallyFiniteMeasure airyMeasure := isLocallyFinite_airyMeasure
    refine lt_of_le_of_lt (measure_mono Ioo_subset_Icc_self) ?_
    rw [smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top isCompact_Icc.measure_lt_top⟩⟩

private lemma tendsto_measure_isolating_of_vagueLimit
    {μ : ℕ → Measure ℝ} [∀ j, IsLocallyFiniteMeasure (μ j)]
    {c : ℝ} (hc : 0 < c) (hvag : IsVagueLimit atTop μ (ENNReal.ofReal c • airyMeasure))
    {I : Set ℝ} (hbd : Bornology.IsBounded I) {k : ℕ} (hk : airyNode k ∈ interior I)
    (hiso : closure I ∩ Set.range airyNode ⊆ {airyNode k}) :
    Tendsto (fun j => (μ j I).toReal) atTop (𝓝 (c * airyNodeWeight k)) := by
  have : IsLocallyFiniteMeasure (ENNReal.ofReal c • airyMeasure) := isLocallyFinite_smul_airyMeasure c
  have hν_range : (ENNReal.ofReal c • airyMeasure) (Set.range airyNode)ᶜ = 0 := by
    simp [airyMeasure_compl_range]
  have hsingle_val : ((ENNReal.ofReal c • airyMeasure) {airyNode k}).toReal = c * airyNodeWeight k :=
    (airyMeasure_singleton_mul hc.le hk hiso).2
  have hcl_val : ((ENNReal.ofReal c • airyMeasure) (closure I)).toReal = c * airyNodeWeight k :=
    (airyMeasure_singleton_mul hc.le hk hiso).1
  rw [tendsto_order]
  exact ⟨fun _ ha => tendsto_measure_isolating_lower hbd hk hiso hν_range hsingle_val hvag ha,
    fun _ hb => tendsto_measure_isolating_upper hbd hcl_val hvag hb⟩

private lemma quotient_tendsto_of_vagueLimits
    {μ₁ μ₂ : ℕ → Measure ℝ} [∀ j, IsLocallyFiniteMeasure (μ₁ j)]
    [∀ j, IsLocallyFiniteMeasure (μ₂ j)]
    {v : ℝ} (hv : 0 < v)
    (h₁ : IsVagueLimit atTop μ₁ (ENNReal.ofReal v • airyMeasure))
    (h₂ : IsVagueLimit atTop μ₂ airyMeasure)
    {I : Set ℝ} (hbd : Bornology.IsBounded I) {k : ℕ} (hk : airyNode k ∈ interior I)
    (hiso : closure I ∩ Set.range airyNode ⊆ {airyNode k}) :
    Tendsto (fun j => (μ₁ j I).toReal / (μ₂ j I).toReal) atTop (𝓝 v) := by
  have h₂' : IsVagueLimit atTop μ₂ (ENNReal.ofReal 1 • airyMeasure) := by
    simpa only [ENNReal.ofReal_one, one_smul] using h₂
  have hNum := tendsto_measure_isolating_of_vagueLimit hv h₁ hbd hk hiso
  have hDen := tendsto_measure_isolating_of_vagueLimit one_pos h₂' hbd hk hiso
  have hw0 := (airyNodeWeight_pos k).ne'
  have hlim_eq : (v * airyNodeWeight k) / (1 * airyNodeWeight k) = v := by field_simp [hw0]
  rw [← hlim_eq]
  exact hNum.div hDen (by simp [hw0])

/-- **`sd:spinmoment` (cluster second-moment ratio)** (`spinning_airy_moment.tex`, Theorem
SD-M2, eq. `sd:spinmoment-ratio`): for any bounded set `I` whose closure meets `Set.range airyNode`
only at `airyNode k ∈ interior I`, the ratio of the spin-moment spectral measure of `I` to the
scalar radial spectral measure of `I` converges to `spinMomentVStar = 2 * xiStar ^ 3 / (3 * π)`. -/
theorem spinMoment_cluster_ratio_tendsto
    (cSeq τSeq BSeq : ℕ → ℝ) (hc : Tendsto cSeq atTop atTop) (hc25 : ∀ j, 25 ≤ cSeq j)
    (hτ : ∀ j, 0 < τSeq j) (hB : ∀ j, 0 ≤ BSeq j)
    (hGap : GapCondition (fun j => cSeq j - 1) τSeq)
    (meas : ∀ j, SpinCrossingMeasureOn ((cSeq j - 1) / 12)
      (spinConeB (BSeq j) ∩ {p : ℝ × ℝ | τSeq j ≤ p.1 + p.2}))
    {I : Set ℝ} (hbd : Bornology.IsBounded I) {k : ℕ} (hk : airyNode k ∈ interior I)
    (hiso : closure I ∩ Set.range airyNode ⊆ {airyNode k}) :
    Tendsto (fun j =>
      (spinMomentSpectralMeasure (cSeq j - 1) (meas j).ν I).toReal /
        (spectralMeasure virasoroProblem (cSeq j - 1) (spinRadMarginal (meas j).ν) I).toReal)
      atTop (𝓝 spinMomentVStar) := by
  have hlf_num : ∀ j, IsLocallyFiniteMeasure (spinMomentSpectralMeasure (cSeq j - 1) (meas j).ν) :=
    fun j => spinMomentSpectralMeasure_isLocallyFinite (by linarith [hc25 j]) (by linarith [hc25 j])
      (hB j) (hτ j) Subset.rfl (meas j)
  have hlf_den : ∀ j, IsLocallyFiniteMeasure
      (spectralMeasure virasoroProblem (cSeq j - 1) (spinRadMarginal (meas j).ν)) := fun j => by
    have hc'0 : 0 < cSeq j - 1 := by linarith [hc25 j]
    have ha_vir : virasoroProblem.totalShift ≤ (cSeq j - 1) / 12 := by
      rw [virasoroProblem_totalShift]; linarith [hc25 j]
    let rad := (meas j).toRadAdmissible (fun _ (hp : _ ∈ spinConeB (BSeq j) ∩ {p | τSeq j ≤ p.1 + p.2}) =>
      (hτ j).le.trans hp.2)
    let hrad := (meas j).toRadAdmissible_atGap (hτ j).le
      (fun _ (hp : _ ∈ spinConeB (BSeq j) ∩ {p | τSeq j ≤ p.1 + p.2}) => hp.2)
    exact isLocallyFiniteMeasure_spectralMeasure virasoroProblem hc'0 ha_vir rad (hτ j) hrad
  exact @quotient_tendsto_of_vagueLimits
    (fun j => spinMomentSpectralMeasure (cSeq j - 1) (meas j).ν)
    (fun j => spectralMeasure virasoroProblem (cSeq j - 1) (spinRadMarginal (meas j).ν))
    hlf_num hlf_den spinMomentVStar spinMomentVStar_pos
    (spinMoment_vagueLimit cSeq τSeq BSeq hc hc25 hτ hB hGap meas)
    (spinDR cSeq τSeq BSeq hc hc25 hτ hB hGap meas).2.2.2.1 I hbd k hk hiso

/-- info: 'FormalResearch.ModularBootstrap.Spin.spinMoment_cluster_ratio_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms spinMoment_cluster_ratio_tendsto

end FormalResearch.ModularBootstrap.Spin
