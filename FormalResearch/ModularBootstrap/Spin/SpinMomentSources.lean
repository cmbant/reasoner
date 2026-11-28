module

public import FormalResearch.ModularBootstrap.Spin.SpinMomentEndpoint
public import FormalResearch.ModularBootstrap.Spin.SpinDAssembly

/-!
# Source limit and window-pairing upper bound for `SPIN-M`

Source: `CFT/modular_bootstrap/paper/spinning_airy_moment_proof.tex`
(`sd:spinmoment-volterra-limit`, `sd:spinmoment-window-pair`).

* `spinMoment_volterra_source_tendsto` (`sd:spinmoment-volterra-limit`):
  `(∫ K^* g₅ dν₀) / (π c' C_* FKc 1 1 c') → (ξ_*^3 / (3π)) V_D`.
* `spinMoment_window_pair_limsup_le` (`sd:spinmoment-window-pair`):
  `limsup_{j→∞} ∫ Ψ₅ dη_j ≤ v_* V_D`, where `v_* = 2 ξ_*^3 / (3π)`.
-/

@[expose] public section

open Real Filter Topology Set MeasureTheory
open scoped Real ENNReal

namespace FormalResearch.ModularBootstrap.Spin

open FormalResearch.Special
open FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.Upper
open FormalResearch.ModularBootstrap.Upper.Rigidity
open FormalResearch.ModularBootstrap.Upper.Assembly
open FormalResearch.ModularBootstrap.Upper.Positivity
open FormalResearch.ModularBootstrap.Upper.Design
open FormalResearch.ModularBootstrap.Upper.Window
open FormalResearch.ModularBootstrap.Upper.Window.Cardy
open FormalResearch.ModularBootstrap.Upper.Bump
open FormalResearch.ModularBootstrap.Upper.Comb

/-- Leading moment coefficient `v_* = 2 ξ_*^3 / (3π)` in Theorem `sd:spinmoment`. -/
noncomputable def spinMomentVStar : ℝ := 2 * xiStar ^ 3 / (3 * π)

lemma spinMomentVStar_pos : 0 < spinMomentVStar := by
  unfold spinMomentVStar
  have := xiStar_pos
  have := Real.pi_pos
  positivity

lemma sum_airyMeasure_window (D : Window) :
    ∫ u, D.W u ∂airyMeasure = D.V := by
  have h1 := integral_airyMeasure D.continuous D.hasSum.summable
  exact h1.trans D.hasSum.tsum_eq

lemma windowIntegralSig_eq_windowV (N : ℕ) (η : ℝ) (σs : ℕ → ℝ) (D : Window)
    (hW : D.W = sigWinW N η σs) :
    windowIntegralSig N η σs = D.V := by
  unfold windowIntegralSig Window.V
  rw [hW]
  rfl

private lemma kappaAiry_eq_betaTip_mul_kTip :
    betaTip * kTip ^ (-(2 / 3 : ℝ)) = kappaAiry := by
  unfold betaTip KTip kappaAiry
  have hpi := Real.pi_pos
  have hk := kTip_pos
  rw [show 3 * (2 * π * kTip) / 4 = (3 * π / 2) * kTip by ring,
    Real.mul_rpow (by positivity) hk.le, mul_assoc, ← Real.rpow_add hk]
  norm_num

private lemma cutoff_eq_one_of_mem {A B u : ℝ} (hA : A ≤ u) (hB : u ≤ B) :
    cutoff A B u = 1 := by
  unfold cutoff
  have h1 : 1 ≤ u - A + 1 := by linarith
  have h2 : 1 ≤ B + 1 - u := by linarith
  rw [min_eq_left (le_min h1 h2), max_eq_right zero_le_one]

private lemma cutoff_eq_zero_of_not_mem {A B u : ℝ} (hu : u ∉ Icc (A - 1) (B + 1)) :
    cutoff A B u = 0 := by
  unfold cutoff
  rw [mem_Icc, not_and_or, not_le, not_le] at hu
  have hm : min (u - A + 1) (B + 1 - u) ≤ 0 := by
    rcases hu with h | h
    · exact (min_le_left _ _).trans (by linarith)
    · exact (min_le_right _ _).trans (by linarith)
  exact max_eq_left ((min_le_right _ _).trans hm)

private lemma hasCompactSupport_cutoff_mul {A B : ℝ} (f : ℝ → ℝ) :
    HasCompactSupport (fun u => cutoff A B u * f u) :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := A - 1) (b := B + 1))
    fun u hu => by
      by_contra hnot
      exact hu (by simp [cutoff_eq_zero_of_not_mem hnot])

private lemma airy_cutoff_tail (D : Window) {ε : ℝ} (hε : 0 < ε) :
    ∃ R_Ai : ℝ, 0 ≤ R_Ai ∧ ∀ R : ℝ, R_Ai ≤ R →
      |∫ u, cutoff (-R) (airyZero 1 + 1) u * ((xiStar ^ 3 / (3 * π)) * D.W u) ∂airyMeasure -
        (xiStar ^ 3 / (3 * π)) * D.V| ≤ ε := by
  have hpi := Real.pi_pos
  have hξ := xiStar_pos
  set c_fac := xiStar ^ 3 / (3 * π)
  have hc_pos : 0 < c_fac := by positivity
  have hs_abs : Summable fun i : ℕ => |D.W (airyNode i)| * airyNodeWeight i := by
    refine D.hasSum.summable.abs.congr fun i => ?_
    rw [abs_mul, abs_of_pos (airyNodeWeight_pos i)]
  have ht_tail : Tendsto (fun n : ℕ => ∑' k : ℕ, |D.W (airyNode (k + n))| * airyNodeWeight (k + n))
      atTop (nhds 0) := by
    have hsum_eq : ∀ n : ℕ,
        ∑' k : ℕ, |D.W (airyNode (k + n))| * airyNodeWeight (k + n) =
          (∑' i : ℕ, |D.W (airyNode i)| * airyNodeWeight i) -
            ∑ i ∈ Finset.range n, |D.W (airyNode i)| * airyNodeWeight i := fun n => by
      have h := hs_abs.sum_add_tsum_nat_add n
      linarith
    simp_rw [hsum_eq]
    simpa [sub_self] using
      (tendsto_const_nhds (x := ∑' i : ℕ, |D.W (airyNode i)| * airyNodeWeight i)).sub
        hs_abs.hasSum.tendsto_sum_nat
  obtain ⟨I₀, hI₀⟩ := ((ht_tail.const_mul c_fac).eventually_le_const
    (by simpa only [mul_zero] using hε)).exists
  refine ⟨|airyNode I₀| + 1, by positivity, fun R hR => ?_⟩
  have hcont_f : Continuous fun u => cutoff (-R) (airyZero 1 + 1) u * (c_fac * D.W u) :=
    (cutoff_continuous _ _).mul (continuous_const.mul D.continuous)
  have hsum_f : Summable fun i =>
      (cutoff (-R) (airyZero 1 + 1) (airyNode i) * (c_fac * D.W (airyNode i))) * airyNodeWeight i := by
    refine Summable.of_norm_bounded (Summable.mul_left c_fac hs_abs) fun i => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_pos hc_pos,
      abs_of_pos (airyNodeWeight_pos i)]
    have hc1 : |cutoff (-R) (airyZero 1 + 1) (airyNode i)| ≤ 1 :=
      abs_le.mpr ⟨by linarith [cutoff_nonneg (-R) (airyZero 1 + 1) (airyNode i)],
        cutoff_le_one _ _ _⟩
    have hwnn : 0 ≤ airyNodeWeight i := (airyNodeWeight_pos i).le
    calc |cutoff (-R) (airyZero 1 + 1) (airyNode i)| * (c_fac * |D.W (airyNode i)|) *
          airyNodeWeight i
        ≤ 1 * (c_fac * |D.W (airyNode i)|) * airyNodeWeight i := by gcongr
      _ = c_fac * (|D.W (airyNode i)| * airyNodeWeight i) := by ring
  rw [integral_airyMeasure hcont_f hsum_f]
  have hV_sum : Summable fun i => (c_fac * D.W (airyNode i)) * airyNodeWeight i := by
    simpa [mul_assoc] using D.hasSum.summable.mul_left c_fac
  have hV_eq : c_fac * D.V = ∑' i, (c_fac * D.W (airyNode i)) * airyNodeWeight i := by
    unfold Window.V
    rw [← D.hasSum.tsum_eq, ← tsum_mul_left]
    exact tsum_congr fun i => by ring
  rw [hV_eq, ← hsum_f.tsum_sub hV_sum]
  have hdiff_sum : Summable fun i =>
      (cutoff (-R) (airyZero 1 + 1) (airyNode i) - 1) * (c_fac * D.W (airyNode i)) *
        airyNodeWeight i :=
    (hsum_f.sub hV_sum).congr fun i => by ring
  have hrew : (∑' i, ((cutoff (-R) (airyZero 1 + 1) (airyNode i) * (c_fac * D.W (airyNode i))) *
        airyNodeWeight i - (c_fac * D.W (airyNode i)) * airyNodeWeight i)) =
      ∑' i, (cutoff (-R) (airyZero 1 + 1) (airyNode i) - 1) * (c_fac * D.W (airyNode i)) *
        airyNodeWeight i := tsum_congr fun i => by ring
  rw [hrew, ← hdiff_sum.sum_add_tsum_nat_add I₀]
  have hzero : ∑ i ∈ Finset.range I₀,
      (cutoff (-R) (airyZero 1 + 1) (airyNode i) - 1) * (c_fac * D.W (airyNode i)) *
        airyNodeWeight i = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    have hi_le : i ≤ I₀ := (Finset.mem_range.mp hi).le
    have hlow : -R ≤ airyNode i := by
      have h1 : airyNode I₀ ≤ airyNode i := airyNode_strictAnti.antitone hi_le
      have h2 : -R ≤ -(|airyNode I₀| + 1) := by linarith
      linarith [neg_abs_le (airyNode I₀)]
    have hhi : airyNode i ≤ airyZero 1 + 1 := by
      have h1 := airyNode_le_airyNode_zero i
      linarith
    rw [cutoff_eq_one_of_mem hlow hhi, sub_self, zero_mul, zero_mul]
  rw [hzero, zero_add]
  have hs_tail : Summable fun k =>
      (cutoff (-R) (airyZero 1 + 1) (airyNode (k + I₀)) - 1) *
        (c_fac * D.W (airyNode (k + I₀))) * airyNodeWeight (k + I₀) :=
    (summable_nat_add_iff I₀).2 hdiff_sum
  have hs_bd : Summable fun k =>
      c_fac * (|D.W (airyNode (k + I₀))| * airyNodeWeight (k + I₀)) :=
    Summable.mul_left c_fac ((summable_nat_add_iff I₀).2 hs_abs)
  have hnorm_le := norm_tsum_le_tsum_norm hs_tail.norm
  rw [Real.norm_eq_abs] at hnorm_le
  calc |∑' k, (cutoff (-R) (airyZero 1 + 1) (airyNode (k + I₀)) - 1) *
          (c_fac * D.W (airyNode (k + I₀))) * airyNodeWeight (k + I₀)|
      ≤ ∑' k, ‖(cutoff (-R) (airyZero 1 + 1) (airyNode (k + I₀)) - 1) *
          (c_fac * D.W (airyNode (k + I₀))) * airyNodeWeight (k + I₀)‖ := hnorm_le
    _ ≤ ∑' k, c_fac * (|D.W (airyNode (k + I₀))| * airyNodeWeight (k + I₀)) := by
        refine Summable.tsum_le_tsum (fun k => ?_) hs_tail.norm hs_bd
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_pos hc_pos,
          abs_of_pos (airyNodeWeight_pos (k + I₀))]
        have hcut : |cutoff (-R) (airyZero 1 + 1) (airyNode (k + I₀)) - 1| ≤ 1 := by
          have := cutoff_nonneg (-R) (airyZero 1 + 1) (airyNode (k + I₀))
          have := cutoff_le_one (-R) (airyZero 1 + 1) (airyNode (k + I₀))
          exact abs_le.mpr ⟨by linarith, by linarith⟩
        have hwnn : 0 ≤ airyNodeWeight (k + I₀) := (airyNodeWeight_pos (k + I₀)).le
        calc |cutoff (-R) (airyZero 1 + 1) (airyNode (k + I₀)) - 1| *
              (c_fac * |D.W (airyNode (k + I₀))|) * airyNodeWeight (k + I₀)
            ≤ 1 * (c_fac * |D.W (airyNode (k + I₀))|) * airyNodeWeight (k + I₀) := by gcongr
          _ = c_fac * (|D.W (airyNode (k + I₀))| * airyNodeWeight (k + I₀)) := by ring
    _ = c_fac * ∑' k, |D.W (airyNode (k + I₀))| * airyNodeWeight (k + I₀) := by rw [← tsum_mul_left]
    _ ≤ ε := hI₀

private lemma mid_band_abs_integral_le {c' C_mid Sg0 R δ : ℝ} (hc' : 0 < c')
    (ha : virasoroProblem.totalShift ≤ c' / 12) (hCmid : 0 < C_mid) (_hSg0 : 0 < Sg0)
    (hR : kappaAiry * Sg0 ≤ R) (hδ : 0 ≤ δ)
    (ν₀ : Measure ℝ) (g₅ g₁ T_Ψ : ℝ → ℝ)
    (hg5_int : IntegrableOn (spinVolterraAdjoint g₅) (Ici 0) ν₀)
    (hT_cont : Continuous T_Ψ)
    (hT_eq : T_Ψ = fun u => psiScale virasoroProblem c' * psiAiry virasoroProblem c' g₁ u)
    (hT_nn : ∀ u, u ≤ -R → 0 ≤ T_Ψ u)
    (hT_int : Integrable T_Ψ (spectralMeasure virasoroProblem c' ν₀))
    (hdom : ∀ x : ℝ, xiStar + lambdaComb c' * Sg0 ≤ x → x ≤ xiStar + 1 →
      0 < g₁ (c' * x ^ 2 / 3) ∧
        |spinVolterraAdjoint g₅ (c' * x ^ 2 / 3)| ≤ C_mid * c' * g₁ (c' * x ^ 2 / 3))
    (hnoesc : ∫ u in Iio (-R), T_Ψ u ∂(spectralMeasure virasoroProblem c' ν₀) ≤ δ) :
    (∫ r in {r : ℝ | 0 < r ∧ uAiry c' r < -R ∧ r ≤ c' * (xiStar + 1) ^ 2 / 3},
        |spinVolterraAdjoint g₅ r| ∂ν₀) / (π * c' * CStar * FKc 1 1 c') ≤ C_mid * δ := by
  have hpi := Real.pi_pos
  have hCS := CStar_pos
  have hFK := FKc_pos zero_lt_one 1 hc'
  set S_scale := π * c' * CStar * FKc 1 1 c'
  have hSs_pos : 0 < S_scale := by positivity
  set s := {r : ℝ | 0 < r ∧ uAiry c' r < -R ∧ r ≤ c' * (xiStar + 1) ^ 2 / 3}
  have hs_meas : MeasurableSet s :=
    (measurableSet_Ioi (a := (0 : ℝ))).inter
      (((continuous_uAiry c').measurable measurableSet_Iio).inter measurableSet_Iic)
  have hs_sub : s ⊆ Ici 0 := fun _ hr => hr.1.le
  have hs_Ioi : s ⊆ Ioi 0 := fun _ hr => hr.1
  have hφ_int : Integrable (Set.indicator (Iio (-R)) T_Ψ)
      (spectralMeasure virasoroProblem c' ν₀) := hT_int.indicator measurableSet_Iio
  have hφ_nn : ∀ u, 0 ≤ Set.indicator (Iio (-R)) T_Ψ u := fun u => by
    by_cases hu : u ∈ Iio (-R)
    · rw [Set.indicator_of_mem hu]; exact hT_nn u (mem_Iio.mp hu).le
    · rw [Set.indicator_of_notMem hu]
  have hl_eq : ∫⁻ u, ENNReal.ofReal (Set.indicator (Iio (-R)) T_Ψ u)
      ∂(spectralMeasure virasoroProblem c' ν₀) =
      ENNReal.ofReal (∫ u in Iio (-R), T_Ψ u ∂(spectralMeasure virasoroProblem c' ν₀)) := by
    rw [← MeasureTheory.integral_indicator measurableSet_Iio,
      MeasureTheory.ofReal_integral_eq_lintegral_ofReal hφ_int (Eventually.of_forall hφ_nn)]
  have hl_map : ∫⁻ u, ENNReal.ofReal (Set.indicator (Iio (-R)) T_Ψ u)
      ∂(spectralMeasure virasoroProblem c' ν₀) =
      ∫⁻ r in Ioi 0, spectralDensity virasoroProblem c' r *
        ENNReal.ofReal (Set.indicator (Iio (-R)) T_Ψ (uAiry c' r)) ∂ν₀ := by
    unfold spectralMeasure
    have hmeas_φ : Measurable fun u => ENNReal.ofReal (Set.indicator (Iio (-R)) T_Ψ u) :=
      ENNReal.measurable_ofReal.comp (hT_cont.measurable.indicator measurableSet_Iio)
    have hcomp : Measurable (fun r => ENNReal.ofReal (Set.indicator (Iio (-R)) T_Ψ (uAiry c' r))) :=
      hmeas_φ.comp (continuous_uAiry c').measurable
    rw [lintegral_map hmeas_φ (continuous_uAiry c').measurable]
    change ∫⁻ r, (fun r => ENNReal.ofReal (Set.indicator (Iio (-R)) T_Ψ (uAiry c' r))) r
        ∂(ν₀.restrict (Ioi 0)).withDensity (spectralDensity virasoroProblem c') = _
    rw [lintegral_withDensity_eq_lintegral_mul (ν₀.restrict (Ioi 0))
      (measurable_spectralDensity virasoroProblem c') hcomp]
    rfl
  have hpt : ∀ r ∈ s,
      ENNReal.ofReal (|spinVolterraAdjoint g₅ r| / S_scale) ≤
        ENNReal.ofReal C_mid * (spectralDensity virasoroProblem c' r *
          ENNReal.ofReal (Set.indicator (Iio (-R)) T_Ψ (uAiry c' r))) := by
    rintro r ⟨hr0, hu_lt, hr_hi⟩
    set y := √(3 * r / c')
    have hy0 : 0 < y := Real.sqrt_pos.mpr (by positivity)
    have hr_eq : c' * y ^ 2 / 3 = r := by
      rw [Real.sq_sqrt (by positivity)]; field_simp
    have hy_hi : y ≤ xiStar + 1 := by
      rw [Real.sqrt_le_iff]
      exact ⟨by linarith [xiStar_pos], (div_le_iff₀ hc').mpr (by linarith)⟩
    have hy_lo : xiStar + lambdaComb c' * Sg0 ≤ y := by
      have hu_eq : uAiry c' r = -betaTip * (y - xiStar) * c' ^ ((2 : ℝ) / 3) := by
        unfold uAiry; rfl
      have hprod : betaTip * c' ^ ((2 : ℝ) / 3) * (lambdaComb c' * Sg0) = kappaAiry * Sg0 := by
        unfold lambdaComb
        rw [Real.mul_rpow kTip_pos.le hc'.le,
          show betaTip * c' ^ ((2 : ℝ) / 3) * (kTip ^ (-(2 / 3 : ℝ)) * c' ^ (-(2 / 3 : ℝ)) * Sg0) =
            (betaTip * kTip ^ (-(2 / 3 : ℝ))) * (c' ^ ((2 : ℝ) / 3) * c' ^ (-(2 / 3 : ℝ))) * Sg0 by ring,
          kappaAiry_eq_betaTip_mul_kTip, ← Real.rpow_add hc', show (2 : ℝ) / 3 + -(2 / 3) = 0 by norm_num,
          Real.rpow_zero, mul_one]
      have hbc : 0 < betaTip * c' ^ ((2 : ℝ) / 3) := mul_pos betaTip_pos (Real.rpow_pos_of_pos hc' _)
      have h1 : kappaAiry * Sg0 < betaTip * c' ^ ((2 : ℝ) / 3) * (y - xiStar) := by
        rw [hu_eq] at hu_lt; linarith
      rw [← hprod] at h1
      have h2 : lambdaComb c' * Sg0 < y - xiStar :=
        lt_of_not_ge fun h => not_lt_of_ge (mul_le_mul_of_nonneg_left h hbc.le) h1
      linarith
    obtain ⟨_, hdom_y⟩ := hdom y hy_lo hy_hi
    rw [hr_eq] at hdom_y
    have hsw : spectralWeight virasoroProblem c' r * T_Ψ (uAiry c' r) =
        c' * g₁ r / S_scale := by
      rw [hT_eq, mul_left_comm, weight_mul_psiAiry hc' ha g₁ hr0]
      unfold psiScale
      have hFK0 : FKc (qProb virasoroProblem) 1 c' = FKc 1 1 c' := by rw [qProb_virasoro]
      rw [hFK0]
      have hcs0 := CStar_pos.ne'
      have hfk0 := hFK.ne'
      have hpi0 := Real.pi_pos.ne'
      have hc0 := hc'.ne'
      dsimp [S_scale]
      field_simp
    have hT_r_nn : 0 ≤ T_Ψ (uAiry c' r) := hT_nn _ hu_lt.le
    have hsw_nn : 0 ≤ spectralWeight virasoroProblem c' r :=
      (spectralWeight_pos hc' ha hr0).le
    unfold spectralDensity
    rw [Set.indicator_of_mem (mem_Iio.mpr hu_lt), ← ENNReal.ofReal_mul hsw_nn,
      ← ENNReal.ofReal_mul hCmid.le]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hsw]
    calc |spinVolterraAdjoint g₅ r| / S_scale
        ≤ (C_mid * c' * g₁ r) / S_scale := div_le_div_of_nonneg_right hdom_y hSs_pos.le
      _ = C_mid * (c' * g₁ r / S_scale) := by ring
  have hl_int : ∫⁻ r in s, ENNReal.ofReal (|spinVolterraAdjoint g₅ r| / S_scale) ∂ν₀ =
      ENNReal.ofReal ((∫ r in s, |spinVolterraAdjoint g₅ r| ∂ν₀) / S_scale) := by
    have hsub_int : IntegrableOn (fun r => |spinVolterraAdjoint g₅ r| / S_scale) s ν₀ :=
      ((hg5_int.mono_set hs_sub).abs.div_const S_scale)
    rw [← MeasureTheory.integral_div,
      MeasureTheory.ofReal_integral_eq_lintegral_ofReal hsub_int
        (Eventually.of_forall fun _ => div_nonneg (abs_nonneg _) hSs_pos.le)]
  have hl_le : ∫⁻ r in s, ENNReal.ofReal (|spinVolterraAdjoint g₅ r| / S_scale) ∂ν₀ ≤
      ENNReal.ofReal (C_mid * δ) := by
    calc ∫⁻ r in s, ENNReal.ofReal (|spinVolterraAdjoint g₅ r| / S_scale) ∂ν₀
        ≤ ∫⁻ r in s, ENNReal.ofReal C_mid * (spectralDensity virasoroProblem c' r *
            ENNReal.ofReal (Set.indicator (Iio (-R)) T_Ψ (uAiry c' r))) ∂ν₀ :=
          setLIntegral_mono' hs_meas hpt
      _ = ENNReal.ofReal C_mid * ∫⁻ r in s, spectralDensity virasoroProblem c' r *
            ENNReal.ofReal (Set.indicator (Iio (-R)) T_Ψ (uAiry c' r)) ∂ν₀ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal C_mid * ∫⁻ r in Ioi 0, spectralDensity virasoroProblem c' r *
            ENNReal.ofReal (Set.indicator (Iio (-R)) T_Ψ (uAiry c' r)) ∂ν₀ := by
          gcongr
      _ = ENNReal.ofReal C_mid *
            ENNReal.ofReal (∫ u in Iio (-R), T_Ψ u ∂(spectralMeasure virasoroProblem c' ν₀)) := by
          rw [← hl_map, hl_eq]
      _ ≤ ENNReal.ofReal C_mid * ENNReal.ofReal δ := by
          gcongr
      _ = ENNReal.ofReal (C_mid * δ) := (ENNReal.ofReal_mul hCmid.le).symm
  rw [hl_int] at hl_le
  have h1 := ENNReal.toReal_mono ENNReal.ofReal_ne_top hl_le
  rwa [ENNReal.toReal_ofReal (div_nonneg (integral_nonneg fun _ => abs_nonneg _) hSs_pos.le),
    ENNReal.toReal_ofReal (mul_nonneg hCmid.le hδ)] at h1

private lemma noncutoff_volterra_tail_le {c' τ B C_mid Sg0 R δ_noesc δ_far : ℝ}
    (hc' : 0 < c') (ha : virasoroProblem.totalShift ≤ c' / 12) (hτ : 0 < τ)
    (hCmid : 0 < C_mid) (hSg0 : 0 < Sg0) (hR : kappaAiry * Sg0 ≤ R)
    (hδ1 : 0 ≤ δ_noesc) (_hδ2 : 0 ≤ δ_far)
    (meas : SpinCrossingMeasureOn (c' / 12) (spinConeB B ∩ {p | τ ≤ p.1 + p.2}))
    (hτ_hi : uAiry c' τ ≤ airyZero 1 + 1)
    (g₅ g₁ T_Ψ : ℝ → ℝ)
    (hg5_int : IntegrableOn (spinVolterraAdjoint g₅) (Ici 0) (spinRadMarginal meas.ν))
    (hT_cont : Continuous T_Ψ)
    (hT_eq : T_Ψ = fun u => psiScale virasoroProblem c' * psiAiry virasoroProblem c' g₁ u)
    (hT_nn : ∀ u, u ≤ -R → 0 ≤ T_Ψ u)
    (hT_int : Integrable T_Ψ (spectralMeasure virasoroProblem c' (spinRadMarginal meas.ν)))
    (hdom : ∀ x : ℝ, xiStar + lambdaComb c' * Sg0 ≤ x → x ≤ xiStar + 1 →
      0 < g₁ (c' * x ^ 2 / 3) ∧
        |spinVolterraAdjoint g₅ (c' * x ^ 2 / 3)| ≤ C_mid * c' * g₁ (c' * x ^ 2 / 3))
    (hnoesc : ∫ u in Iio (-R), T_Ψ u
        ∂(spectralMeasure virasoroProblem c' (spinRadMarginal meas.ν)) ≤ δ_noesc)
    (hfar : (∫ r in Ici (c' * (xiStar + 1) ^ 2 / 3),
        |spinVolterraAdjoint g₅ r| ∂(spinRadMarginal meas.ν)) /
        (π * c' * CStar * FKc 1 1 c') ≤ δ_far) :
    |∫ r in Ici (0 : ℝ), (1 - cutoff (-R) (airyZero 1 + 1) (uAiry c' r)) *
        spinVolterraAdjoint g₅ r ∂(spinRadMarginal meas.ν)| /
        (π * c' * CStar * FKc 1 1 c') ≤ C_mid * δ_noesc + δ_far := by
  have hpi := Real.pi_pos
  have hCS := CStar_pos
  have hFK := FKc_pos zero_lt_one 1 hc'
  set ν₀ := spinRadMarginal meas.ν
  set S_scale := π * c' * CStar * FKc 1 1 c'
  have hSs_pos : 0 < S_scale := by positivity
  have hν₀_gap : ν₀ (Iio τ) = 0 :=
    meas.toRadAdmissible_atGap hτ.le (fun _ (hp : _ ∈ spinConeB B ∩ {p | τ ≤ p.1 + p.2}) => hp.2)
  have hν₀_zero : ν₀ {0} = 0 :=
    measure_mono_null (singleton_subset_iff.mpr hτ) hν₀_gap
  have h_ae_zero : ∀ᵐ r ∂ν₀.restrict (Ici 0),
      r ∉ {r : ℝ | 0 < r ∧ uAiry c' r < -R} →
        (1 - cutoff (-R) (airyZero 1 + 1) (uAiry c' r)) * spinVolterraAdjoint g₅ r = 0 := by
    have hmem_Iio := measure_eq_zero_iff_ae_notMem.1 hν₀_gap
    have hmem_0 := measure_eq_zero_iff_ae_notMem.1 hν₀_zero
    filter_upwards [ae_restrict_mem measurableSet_Ici,
      ae_restrict_of_ae hmem_Iio, ae_restrict_of_ae hmem_0] with r hr_Ici hr_ge hr_ne0 hnot
    have hr_pos : 0 < r := lt_of_le_of_ne hr_Ici (Ne.symm (by simpa using hr_ne0))
    have hτ_le : τ ≤ r := not_lt.mp hr_ge
    have hu_hi : uAiry c' r ≤ airyZero 1 + 1 := (uAiry_antitone hc' hτ_le).trans hτ_hi
    have hu_lo : -R ≤ uAiry c' r := by
      by_contra hlt
      exact hnot ⟨hr_pos, not_le.mp hlt⟩
    rw [cutoff_eq_one_of_mem hu_lo hu_hi, sub_self, zero_mul]
  set E := {r : ℝ | 0 < r ∧ uAiry c' r < -R}
  set r_far := c' * (xiStar + 1) ^ 2 / 3
  set s_mid := {r : ℝ | 0 < r ∧ uAiry c' r < -R ∧ r ≤ r_far}
  set s_far := {r : ℝ | 0 < r ∧ uAiry c' r < -R ∧ r_far < r}
  have hE_sub : E ⊆ Ici 0 := fun _ hr => hr.1.le
  have hE_meas : MeasurableSet E :=
    (measurableSet_Ioi (a := (0 : ℝ))).inter ((continuous_uAiry c').measurable measurableSet_Iio)
  have hsm_meas : MeasurableSet s_mid :=
    (measurableSet_Ioi (a := (0 : ℝ))).inter
      (((continuous_uAiry c').measurable measurableSet_Iio).inter measurableSet_Iic)
  have hsf_meas : MeasurableSet s_far :=
    (measurableSet_Ioi (a := (0 : ℝ))).inter
      (((continuous_uAiry c').measurable measurableSet_Iio).inter measurableSet_Ioi)
  have hE_eq : E = s_mid ∪ s_far := by
    ext r; simp only [E, s_mid, s_far, mem_union, mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩; rcases le_or_gt r r_far with h3 | h3
      · exact Or.inl ⟨h1, h2, h3⟩
      · exact Or.inr ⟨h1, h2, h3⟩
    · rintro (⟨h1, h2, _⟩ | ⟨h1, h2, _⟩) <;> exact ⟨h1, h2⟩
  have hdisj : Disjoint s_mid s_far :=
    Set.disjoint_iff.mpr fun r ⟨h1, h2⟩ => not_lt_of_ge h1.2.2 h2.2.2
  have hfn_int : IntegrableOn
      (fun r => (1 - cutoff (-R) (airyZero 1 + 1) (uAiry c' r)) * spinVolterraAdjoint g₅ r)
      (Ici 0) ν₀ := by
    refine hg5_int.abs.mono' (((continuous_const.sub ((cutoff_continuous _ _).comp
      (continuous_uAiry c'))).aestronglyMeasurable.mono_measure Measure.restrict_le_self).mul
      hg5_int.aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ici] with r _
    rw [Real.norm_eq_abs, abs_mul]
    have hc1 : |1 - cutoff (-R) (airyZero 1 + 1) (uAiry c' r)| ≤ 1 := by
      have := cutoff_nonneg (-R) (airyZero 1 + 1) (uAiry c' r)
      have := cutoff_le_one (-R) (airyZero 1 + 1) (uAiry c' r)
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    exact mul_le_of_le_one_left (abs_nonneg _) hc1
  have hint_E : ∫ r in Ici 0, (1 - cutoff (-R) (airyZero 1 + 1) (uAiry c' r)) *
      spinVolterraAdjoint g₅ r ∂ν₀ =
      ∫ r in E, (1 - cutoff (-R) (airyZero 1 + 1) (uAiry c' r)) *
        spinVolterraAdjoint g₅ r ∂ν₀ := by
    rw [← Set.sdiff_union_of_subset hE_sub,
      setIntegral_union disjoint_sdiff_self_left hE_meas
        (hfn_int.mono_set Set.sdiff_subset) (hfn_int.mono_set hE_sub)]
    have hzero_diff : ∫ r in Ici 0 \ E, (1 - cutoff (-R) (airyZero 1 + 1) (uAiry c' r)) *
        spinVolterraAdjoint g₅ r ∂ν₀ = 0 := by
      refine integral_eq_zero_of_ae ?_
      have hres := ae_restrict_of_ae_restrict_of_subset (s := Ici 0 \ E) (t := Ici 0)
        (Set.sdiff_subset (s := Ici 0) (t := E)) h_ae_zero
      filter_upwards [ae_restrict_mem (measurableSet_Ici.diff hE_meas), hres] with r hr1 hr2
      exact hr2 hr1.2
    rw [hzero_diff, zero_add]
  rw [hint_E, hE_eq, setIntegral_union hdisj hsf_meas
    (hfn_int.mono_set (fun _ (hr : _ ∈ s_mid) => hr.1.le))
    (hfn_int.mono_set (fun _ (hr : _ ∈ s_far) => hr.1.le))]
  have hnorm_m : |∫ r in s_mid, (1 - cutoff (-R) (airyZero 1 + 1) (uAiry c' r)) *
      spinVolterraAdjoint g₅ r ∂ν₀| ≤ ∫ r in s_mid, |spinVolterraAdjoint g₅ r| ∂ν₀ := by
    have hn := MeasureTheory.norm_integral_le_integral_norm
      (μ := ν₀.restrict s_mid)
      (fun r => (1 - cutoff (-R) (airyZero 1 + 1) (uAiry c' r)) * spinVolterraAdjoint g₅ r)
    rw [Real.norm_eq_abs] at hn
    refine hn.trans (setIntegral_mono_on (hfn_int.mono_set (fun _ (hr : _ ∈ s_mid) => hr.1.le)).norm
      (hg5_int.mono_set (fun _ (hr : _ ∈ s_mid) => hr.1.le)).abs hsm_meas fun r _ => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    have hc1 : |1 - cutoff (-R) (airyZero 1 + 1) (uAiry c' r)| ≤ 1 := by
      have := cutoff_nonneg (-R) (airyZero 1 + 1) (uAiry c' r)
      have := cutoff_le_one (-R) (airyZero 1 + 1) (uAiry c' r)
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    exact mul_le_of_le_one_left (abs_nonneg _) hc1
  have hnorm_f : |∫ r in s_far, (1 - cutoff (-R) (airyZero 1 + 1) (uAiry c' r)) *
      spinVolterraAdjoint g₅ r ∂ν₀| ≤
      ∫ r in Ici r_far, |spinVolterraAdjoint g₅ r| ∂ν₀ := by
    have hn := MeasureTheory.norm_integral_le_integral_norm
      (μ := ν₀.restrict s_far)
      (fun r => (1 - cutoff (-R) (airyZero 1 + 1) (uAiry c' r)) * spinVolterraAdjoint g₅ r)
    rw [Real.norm_eq_abs] at hn
    have hsf_Ici : s_far ⊆ Ici r_far := fun _ hr => hr.2.2.le
    calc |∫ r in s_far, (1 - cutoff (-R) (airyZero 1 + 1) (uAiry c' r)) *
          spinVolterraAdjoint g₅ r ∂ν₀|
        ≤ ∫ r in s_far, ‖(1 - cutoff (-R) (airyZero 1 + 1) (uAiry c' r)) *
            spinVolterraAdjoint g₅ r‖ ∂ν₀ := hn
      _ ≤ ∫ r in s_far, |spinVolterraAdjoint g₅ r| ∂ν₀ := by
          refine setIntegral_mono_on (hfn_int.mono_set (fun _ (hr : _ ∈ s_far) => hr.1.le)).norm
            (hg5_int.mono_set (fun _ (hr : _ ∈ s_far) => hr.1.le)).abs hsf_meas fun r _ => ?_
          rw [Real.norm_eq_abs, abs_mul]
          have hc1 : |1 - cutoff (-R) (airyZero 1 + 1) (uAiry c' r)| ≤ 1 := by
            have := cutoff_nonneg (-R) (airyZero 1 + 1) (uAiry c' r)
            have := cutoff_le_one (-R) (airyZero 1 + 1) (uAiry c' r)
            exact abs_le.mpr ⟨by linarith, by linarith⟩
          exact mul_le_of_le_one_left (abs_nonneg _) hc1
      _ ≤ ∫ r in Ici r_far, |spinVolterraAdjoint g₅ r| ∂ν₀ := by
          refine setIntegral_mono_set (hg5_int.mono_set ?_).abs
            (Eventually.of_forall fun _ => abs_nonneg _) (Eventually.of_forall hsf_Ici)
          intro r hr; exact (by positivity : 0 ≤ r_far).trans hr
  have hmid_le := mid_band_abs_integral_le hc' ha hCmid hSg0 hR hδ1 ν₀ g₅ g₁ T_Ψ hg5_int
    hT_cont hT_eq hT_nn hT_int hdom hnoesc
  have htri : |∫ r in s_mid, (1 - cutoff (-R) (airyZero 1 + 1) (uAiry c' r)) *
          spinVolterraAdjoint g₅ r ∂ν₀ +
        ∫ r in s_far, (1 - cutoff (-R) (airyZero 1 + 1) (uAiry c' r)) *
          spinVolterraAdjoint g₅ r ∂ν₀| ≤
      |∫ r in s_mid, (1 - cutoff (-R) (airyZero 1 + 1) (uAiry c' r)) *
          spinVolterraAdjoint g₅ r ∂ν₀| +
        |∫ r in s_far, (1 - cutoff (-R) (airyZero 1 + 1) (uAiry c' r)) *
          spinVolterraAdjoint g₅ r ∂ν₀| := abs_add_le _ _
  calc |∫ r in s_mid, (1 - cutoff (-R) (airyZero 1 + 1) (uAiry c' r)) *
          spinVolterraAdjoint g₅ r ∂ν₀ +
        ∫ r in s_far, (1 - cutoff (-R) (airyZero 1 + 1) (uAiry c' r)) *
          spinVolterraAdjoint g₅ r ∂ν₀| / S_scale
      ≤ (|∫ r in s_mid, _ ∂ν₀| + |∫ r in s_far, _ ∂ν₀|) / S_scale :=
        div_le_div_of_nonneg_right htri hSs_pos.le
    _ = |∫ r in s_mid, _ ∂ν₀| / S_scale + |∫ r in s_far, _ ∂ν₀| / S_scale := by ring
    _ ≤ (∫ r in s_mid, |spinVolterraAdjoint g₅ r| ∂ν₀) / S_scale +
          (∫ r in Ici r_far, |spinVolterraAdjoint g₅ r| ∂ν₀) / S_scale :=
        add_le_add (div_le_div_of_nonneg_right hnorm_m hSs_pos.le)
          (div_le_div_of_nonneg_right hnorm_f hSs_pos.le)
    _ ≤ C_mid * δ_noesc + δ_far := add_le_add hmid_le hfar

/-- **`sd:spinmoment-volterra-limit`**: convergence of the Volterra source term
`(∫ K^* g₅ dν₀) / (π c' C_* FKc 1 1 c') → (ξ_*^3 / (3π)) V_D`. -/
theorem spinMoment_volterra_source_tendsto (N : ℕ) (hN : 1 ≤ N) {η : ℝ} (hη0 : 0 < η)
    (hη1 : η ≤ 1 / 4) (σs : ℕ → ℝ) (D : Window) (hW : D.W = sigWinW N η σs)
    (cSeq τSeq BSeq : ℕ → ℝ) (hc : Tendsto cSeq atTop atTop)
    (hc25 : ∀ j, 25 ≤ cSeq j) (hτ : ∀ j, 0 < τSeq j) (hB : ∀ j, 0 ≤ BSeq j)
    (hGap : GapCondition (fun j => cSeq j - 1) τSeq)
    (meas : ∀ j, SpinCrossingMeasureOn ((cSeq j - 1) / 12)
      (spinConeB (BSeq j) ∩ {p | τSeq j ≤ p.1 + p.2})) :
    Tendsto (fun j =>
      (∫ r in Ici (0 : ℝ),
        spinVolterraAdjoint (bumpG spinMomentW5Prob (rpParams 4).bumpData N η σs (cSeq j - 1)) r
          ∂(spinRadMarginal (meas j).ν)) /
        (π * (cSeq j - 1) * CStar * FKc 1 1 (cSeq j - 1)))
      atTop (nhds ((xiStar ^ 3 / (3 * π)) * D.V)) := by
  let c' : ℕ → ℝ := fun j => cSeq j - 1
  have hc' : Tendsto c' atTop atTop := by
    have : c' = fun j => cSeq j + (-1) := by ext j; ring
    rw [this]; exact hc.atTop_add tendsto_const_nhds
  let S_cross : CrossingSequence virasoroProblem :=
    { c := c'
      τ := τSeq
      meas := fun j => (meas j).toRadAdmissible
        (fun p (hp : p ∈ spinConeB (BSeq j) ∩ {p | τSeq j ≤ p.1 + p.2}) => (hτ j).le.trans hp.2)
      tendsto_c := hc'
      c_pos := fun j => by dsimp [c']; linarith [hc25 j]
      shift_le := fun j => by rw [virasoroProblem_totalShift]; dsimp [c']; linarith [hc25 j]
      τ_pos := hτ
      atGap := fun j => (meas j).toRadAdmissible_atGap (hτ j).le
        (fun _ (hp : _ ∈ spinConeB (BSeq j) ∩ {p | τSeq j ≤ p.1 + p.2}) => hp.2) }
  have hSig := spinDR cSeq τSeq BSeq hc hc25 hτ hB hGap meas
  change SigmaConclusion S_cross.μS at hSig
  set D₁ := designWin 1 (by norm_num : (0 : ℝ) < 1 / 4) 0
  set T₁ := (combDesignData_designW virasoroProblem S_cross 1 le_rfl (by norm_num : (0 : ℝ) < 1 / 4) le_rfl 0).toDesignTest
  set d5 := (rpParams 4).bumpData
  obtain ⟨Sg0, C_mid, hSg0, hCmid, hmid_ev⟩ := spinMoment_mid_band_dom N hN hη0 hη1 σs
  rw [Metric.tendsto_atTop]
  intro ε hε
  refine eventually_atTop.1 ?_
  set δ_noesc := ε / (6 * C_mid)
  have hδ_noesc : 0 < δ_noesc := by positivity
  obtain ⟨R₀, hR₀⟩ := hSig.2.2.2.2 D₁ T₁ δ_noesc hδ_noesc
  obtain ⟨R_Ai, hR_Ai, hAi_tail⟩ := airy_cutoff_tail D (show 0 < ε / 6 by linarith)
  set R := max R₀ (max R_Ai (max (kappaAiry * Sg0 + 1) (|airyZero 1| + 2)))
  have hR_noesc := hR₀ R (le_max_left _ _)
  have hR_Ai' := hAi_tail R (le_trans (le_max_left _ _) (le_max_right _ _))
  have hR_Sg : kappaAiry * Sg0 ≤ R := by
    have : kappaAiry * Sg0 + 1 ≤ max (kappaAiry * Sg0 + 1) (|airyZero 1| + 2) := le_max_left _ _
    have : kappaAiry * Sg0 + 1 ≤ R := this.trans ((le_max_right _ _).trans (le_max_right _ _))
    linarith
  have hR_pos : 0 ≤ R := le_trans (by have := kappaAiry_pos; positivity) hR_Sg
  have hR_theta : -R < airyZero 1 - 1 := by
    have : |airyZero 1| + 2 ≤ R :=
      (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
    linarith [neg_abs_le (airyZero 1)]
  set K := Icc (-(R + 1)) (airyZero 1 + 2)
  set R_end := max (R + 1) (|airyZero 1| + 2)
  have hR_end : 0 ≤ R_end := by positivity
  obtain ⟨M_K, hMK⟩ := hSig.1 K isCompact_Icc
  set M_K' := max M_K 0 + 1
  have hMK'_pos : 0 < M_K' := by positivity
  set δ_end := ε / (6 * M_K')
  have hδ_end : 0 < δ_end := by positivity
  have hend_ev := hc'.eventually (spinMoment_endpoint_tendsto N hN hη0 hη1 σs hR_end hδ_end)
  have hvag_ev : Tendsto (fun j => ∫ u, cutoff (-R) (airyZero 1 + 1) u *
      ((xiStar ^ 3 / (3 * π)) * D.W u) ∂(S_cross.μS j)) atTop
      (nhds (∫ u, cutoff (-R) (airyZero 1 + 1) u * ((xiStar ^ 3 / (3 * π)) * D.W u) ∂airyMeasure)) := by
    refine hSig.2.2.2.1 _ ((cutoff_continuous _ _).mul (continuous_const.mul D.continuous))
      (hasCompactSupport_cutoff_mul _)
  have hvag_near := hvag_ev.eventually (Metric.ball_mem_nhds _ (show 0 < ε / 6 by linarith))
  have hfar_ev := (spinMoment_volterra_tail_far N hN hη0.le hη1 σs c' τSeq BSeq hc' hGap hτ hB meas).div_const
    (π * CStar)
  have hfar_ev' : Tendsto (fun j =>
      (∫ r in Ici (c' j * (xiStar + 1) ^ 2 / 3),
        |spinVolterraAdjoint (bumpG spinMomentW5Prob d5 N η σs (c' j)) r| ∂(spinRadMarginal (meas j).ν)) /
        (π * c' j * CStar * FKc 1 1 (c' j))) atTop (nhds 0) := by
    rw [zero_div] at hfar_ev
    refine hfar_ev.congr fun j => ?_
    have hpi := Real.pi_pos; have hCS := CStar_pos
    have hc'0 : 0 < c' j := by dsimp [c']; linarith [hc25 j]
    have hFK := FKc_pos zero_lt_one 1 hc'0
    dsimp [c', d5]
    field_simp
  have hfar_near := hfar_ev'.eventually (gt_mem_nhds (show 0 < ε / 6 by linarith))
  have hθ_ev : ∀ᶠ j in atTop, -R ≤ T₁.θ j :=
    T₁.theta_tendsto.eventually (lt_mem_nhds (by
      have hD1 : D₁.uF = airyZero 1 := by change airyZero 1 - 0 = airyZero 1; ring
      rw [hD1]; linarith)) |>.mono fun j hj => hj.le
  have hgap_top : ∀ᶠ j in atTop, uAiry (c' j) (τSeq j) ≤ airyZero 1 + 1 :=
    (S_cross.spectralData hGap).gap 1 one_pos
  let E₁ := bumpEventual virasoroProblem 1 le_rfl (by norm_num : (0 : ℝ) < 1 / 4) le_rfl
    (designSigma1 0) (designWin 1 (by norm_num : (0 : ℝ) < 1 / 4) 0)
    (designWin_W_eq_sig 1 (by norm_num) 0) (designWin_uF_eq_sig 1 (by norm_num) 0)
  have hT1_good : ∀ᶠ j in atTop, ∀ u, T₁.Ψ j u = psiScale virasoroProblem (c' j) *
      psiAiry virasoroProblem (c' j)
        (bumpG virasoroProblem (rpParams 0).bumpData 1 (1 / 4) (designSigma1 0) (c' j)) u := by
    filter_upwards [hc'.eventually E₁.good] with j hj u
    change T₁.Ψ j u = E₁.scale (S_cross.c j) * psiAiry virasoroProblem (S_cross.c j) (E₁.g (S_cross.c j)) u
    dsimp [T₁, combDesignData_designW, CombDesignData.toDesignTest, EventualCombData.toComb]
    split_ifs with hg
    · rfl
    · exact absurd hj hg
  have hg5_good := hc'.eventually (bumpG_good spinMomentW5Prob d5 N hN hη0.le hη1 σs)
  have hcont_V_ev := hc'.eventually (continuousOn_spinMomentVolterraScaled N hN hη0.le hη1 σs)
  have hmid_j := hc'.eventually hmid_ev
  filter_upwards [hR_noesc, hMK, hend_ev, hvag_near, hfar_near, hθ_ev, hgap_top, hT1_good,
    hg5_good, hcont_V_ev, hmid_j] with j hnoesc_j hMK_j hend_j hvag_j hfar_j hθ_j hgap_j hT1_j hg5_j hcont_V_j hmid_j
  obtain ⟨hc'0, htest5, C_g, hCg_nn, hdec5⟩ := hg5_j
  have hc24 : 24 ≤ c' j := by dsimp [c']; linarith [hc25 j]
  have ha2 : (2 : ℝ) ≤ c' j / 12 := by linarith
  have ha_vir : virasoroProblem.totalShift ≤ c' j / 12 := by
    rw [virasoroProblem_totalShift]; linarith
  have hdec5' : ∀ t : ℝ, 0 ≤ t → |bumpG spinMomentW5Prob d5 N η σs (c' j) t| ≤
      C_g * Real.exp (-4 * π * Real.sqrt (c' j / 12 * t) - (π * Real.sqrt (3 / c' j)) * Real.sqrt t) := by
    intro t ht
    have hsq : Real.sqrt (3 * t / c' j) = Real.sqrt (3 / c' j) * Real.sqrt t := by
      rw [show 3 * t / c' j = (3 / c' j) * t by ring, Real.sqrt_mul (by positivity)]
    rw [mul_assoc π, ← hsq]; exact hdec5 t ht
  have hpair := spinMoment_pair ha2 (hB j) (hτ j) (fun _ hp => hp) (meas j) htest5
    (by positivity : 0 < π * Real.sqrt (3 / c' j)) hCg_nn hdec5'
  have hg5_int := hpair.2.2.1
  set g₅ := bumpG spinMomentW5Prob d5 N η σs (c' j)
  set ν₀ := spinRadMarginal (meas j).ν
  set S_scale := π * c' j * CStar * FKc 1 1 (c' j)
  have hpi := Real.pi_pos; have hCS := CStar_pos; have hFK := FKc_pos zero_lt_one 1 hc'0
  have hSs_pos : 0 < S_scale := by positivity
  have hχ_split : ∫ r in Ici (0 : ℝ), spinVolterraAdjoint g₅ r ∂ν₀ =
      (∫ r in Ici (0 : ℝ), cutoff (-R) (airyZero 1 + 1) (uAiry (c' j) r) *
        spinVolterraAdjoint g₅ r ∂ν₀) +
      ∫ r in Ici (0 : ℝ), (1 - cutoff (-R) (airyZero 1 + 1) (uAiry (c' j) r)) *
        spinVolterraAdjoint g₅ r ∂ν₀ := by
    have hint1 : IntegrableOn (fun r => cutoff (-R) (airyZero 1 + 1) (uAiry (c' j) r) *
        spinVolterraAdjoint g₅ r) (Ici 0) ν₀ := by
      refine hg5_int.abs.mono' ((((cutoff_continuous _ _).comp
        (continuous_uAiry (c' j))).aestronglyMeasurable.mono_measure Measure.restrict_le_self).mul
        hg5_int.aestronglyMeasurable) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ici] with r _
      rw [Real.norm_eq_abs, abs_mul]
      have hc1 : |cutoff (-R) (airyZero 1 + 1) (uAiry (c' j) r)| ≤ 1 :=
        abs_le.mpr ⟨by linarith [cutoff_nonneg (-R) (airyZero 1 + 1) (uAiry (c' j) r)],
          cutoff_le_one _ _ _⟩
      exact mul_le_of_le_one_left (abs_nonneg _) hc1
    have hint2 : IntegrableOn (fun r => (1 - cutoff (-R) (airyZero 1 + 1) (uAiry (c' j) r)) *
        spinVolterraAdjoint g₅ r) (Ici 0) ν₀ := by
      refine hg5_int.abs.mono' (((continuous_const.sub ((cutoff_continuous _ _).comp
        (continuous_uAiry (c' j)))).aestronglyMeasurable.mono_measure Measure.restrict_le_self).mul
        hg5_int.aestronglyMeasurable) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ici] with r _
      rw [Real.norm_eq_abs, abs_mul]
      have hc1 : |1 - cutoff (-R) (airyZero 1 + 1) (uAiry (c' j) r)| ≤ 1 := by
        have := cutoff_nonneg (-R) (airyZero 1 + 1) (uAiry (c' j) r)
        have := cutoff_le_one (-R) (airyZero 1 + 1) (uAiry (c' j) r)
        exact abs_le.mpr ⟨by linarith, by linarith⟩
      exact mul_le_of_le_one_left (abs_nonneg _) hc1
    rw [← integral_add hint1 hint2]
    refine setIntegral_congr_fun measurableSet_Ici fun r _ => ?_
    ring
  have hχ_spec : (∫ r in Ici (0 : ℝ), cutoff (-R) (airyZero 1 + 1) (uAiry (c' j) r) *
      spinVolterraAdjoint g₅ r ∂ν₀) / S_scale =
      ∫ u, cutoff (-R) (airyZero 1 + 1) u *
        (psiScale virasoroProblem (c' j) *
          psiAiry virasoroProblem (c' j) (spinMomentVolterraScaled d5 N η σs (c' j)) u)
        ∂(S_cross.μS j) := by
    have hν₀_zero : ν₀ {0} = 0 :=
      measure_mono_null (singleton_subset_iff.mpr (hτ j))
        (meas j |>.toRadAdmissible_atGap (hτ j).le
          (fun _ (hp : _ ∈ spinConeB (BSeq j) ∩ {p | τSeq j ≤ p.1 + p.2}) => hp.2))
    have hcont_f : Continuous fun u => cutoff (-R) (airyZero 1 + 1) u *
        (psiScale virasoroProblem (c' j) *
          psiAiry virasoroProblem (c' j) (spinMomentVolterraScaled d5 N η σs (c' j)) u) :=
      (cutoff_continuous _ _).mul (continuous_const.mul (continuous_psiAiry hc'0 hcont_V_j))
    change _ = ∫ u, _ ∂(spectralMeasure virasoroProblem (c' j) ν₀)
    rw [integral_spectralMeasure virasoroProblem hc'0 ha_vir ν₀ hcont_f,
      setIntegral_congr_set (Ioi_ae_eq_Ici' hν₀_zero).symm]
    rw [← integral_div]
    refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
    rw [mul_left_comm (spectralWeight virasoroProblem (c' j) r) (cutoff (-R) (airyZero 1 + 1) (uAiry (c' j) r)),
      mul_left_comm (spectralWeight virasoroProblem (c' j) r) (psiScale virasoroProblem (c' j)),
      weight_mul_psiAiry hc'0 ha_vir _ hr]
    unfold spinMomentVolterraScaled psiScale
    rw [qProb_virasoro]
    have hc0 := hc'0.ne'; have hcs0 := CStar_pos.ne'; have hfk0 := hFK.ne'; have hpi0 := Real.pi_pos.ne'
    dsimp [S_scale]; field_simp; ring
  have hend_diff : |∫ u, cutoff (-R) (airyZero 1 + 1) u *
        (psiScale virasoroProblem (c' j) *
          psiAiry virasoroProblem (c' j) (spinMomentVolterraScaled d5 N η σs (c' j)) u) ∂(S_cross.μS j) -
      ∫ u, cutoff (-R) (airyZero 1 + 1) u * ((xiStar ^ 3 / (3 * π)) * D.W u) ∂(S_cross.μS j)| ≤ ε / 6 := by
    have hint_L : Integrable (fun u => cutoff (-R) (airyZero 1 + 1) u *
        (psiScale virasoroProblem (c' j) *
          psiAiry virasoroProblem (c' j) (spinMomentVolterraScaled d5 N η σs (c' j)) u))
        (S_cross.μS j) := by
      have := S_cross.isLocallyFinite j
      exact ((cutoff_continuous _ _).mul (continuous_const.mul (continuous_psiAiry hc'0
        hcont_V_j))).integrable_of_hasCompactSupport (hasCompactSupport_cutoff_mul _)
    have hint_R : Integrable (fun u => cutoff (-R) (airyZero 1 + 1) u *
        ((xiStar ^ 3 / (3 * π)) * D.W u)) (S_cross.μS j) := by
      have := S_cross.isLocallyFinite j
      exact ((cutoff_continuous _ _).mul (continuous_const.mul D.continuous)).integrable_of_hasCompactSupport
        (hasCompactSupport_cutoff_mul _)
    rw [← integral_sub hint_L hint_R]
    have := S_cross.isLocallyFinite j
    have hsub_supp : HasCompactSupport (fun u => cutoff (-R) (airyZero 1 + 1) u *
        (psiScale virasoroProblem (c' j) *
          psiAiry virasoroProblem (c' j) (spinMomentVolterraScaled d5 N η σs (c' j)) u) -
        cutoff (-R) (airyZero 1 + 1) u * ((xiStar ^ 3 / (3 * π)) * D.W u)) := by
      have heq : (fun u => cutoff (-R) (airyZero 1 + 1) u *
          (psiScale virasoroProblem (c' j) *
            psiAiry virasoroProblem (c' j) (spinMomentVolterraScaled d5 N η σs (c' j)) u) -
          cutoff (-R) (airyZero 1 + 1) u * ((xiStar ^ 3 / (3 * π)) * D.W u)) =
          fun u => cutoff (-R) (airyZero 1 + 1) u *
            (psiScale virasoroProblem (c' j) *
              psiAiry virasoroProblem (c' j) (spinMomentVolterraScaled d5 N η σs (c' j)) u -
            (xiStar ^ 3 / (3 * π)) * D.W u) := by
        ext u; ring
      rw [heq]; exact hasCompactSupport_cutoff_mul _
    have hbd_pt : ∀ u, |cutoff (-R) (airyZero 1 + 1) u *
        (psiScale virasoroProblem (c' j) *
          psiAiry virasoroProblem (c' j) (spinMomentVolterraScaled d5 N η σs (c' j)) u) -
        cutoff (-R) (airyZero 1 + 1) u * ((xiStar ^ 3 / (3 * π)) * D.W u)| ≤ δ_end := by
      intro u
      rw [show cutoff (-R) (airyZero 1 + 1) u * (psiScale virasoroProblem (c' j) *
            psiAiry virasoroProblem (c' j) (spinMomentVolterraScaled d5 N η σs (c' j)) u) -
          cutoff (-R) (airyZero 1 + 1) u * ((xiStar ^ 3 / (3 * π)) * D.W u) =
          cutoff (-R) (airyZero 1 + 1) u *
            (psiScale virasoroProblem (c' j) *
              psiAiry virasoroProblem (c' j) (spinMomentVolterraScaled d5 N η σs (c' j)) u -
            (xiStar ^ 3 / (3 * π)) * D.W u) by ring]
      by_cases hu : u ∈ K
      · have hu_big : u ∈ Icc (-R_end) R_end :=
          ⟨by linarith [hu.1, le_max_left (R + 1) (|airyZero 1| + 2)],
           by linarith [hu.2, le_abs_self (airyZero 1), le_max_right (R + 1) (|airyZero 1| + 2)]⟩
        have h1 := hend_j u hu_big
        rw [← hW] at h1
        rw [abs_mul]
        have hc1 : |cutoff (-R) (airyZero 1 + 1) u| ≤ 1 :=
          abs_le.mpr ⟨by linarith [cutoff_nonneg (-R) (airyZero 1 + 1) u], cutoff_le_one _ _ _⟩
        exact (mul_le_mul hc1 h1 (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
      · have h0 : cutoff (-R) (airyZero 1 + 1) u = 0 :=
          cutoff_eq_zero_of_not_mem (fun hm => hu ⟨by linarith [hm.1], by linarith [hm.2]⟩)
        rw [h0, zero_mul, abs_zero]; exact hδ_end.le
    have htsub : tsupport (fun u => cutoff (-R) (airyZero 1 + 1) u *
        (psiScale virasoroProblem (c' j) *
          psiAiry virasoroProblem (c' j) (spinMomentVolterraScaled d5 N η σs (c' j)) u) -
        cutoff (-R) (airyZero 1 + 1) u * ((xiStar ^ 3 / (3 * π)) * D.W u)) ⊆ K := by
      refine closure_minimal (fun u hu => ?_) isCompact_Icc.isClosed
      by_contra hnot
      have h0 : cutoff (-R) (airyZero 1 + 1) u = 0 := cutoff_eq_zero_of_not_mem
        (fun hm => hnot ⟨by linarith [hm.1], by linarith [hm.2]⟩)
      exact hu (by simp [h0])
    have h1 := abs_integral_le_of_support (μ := S_cross.μS j) hsub_supp hbd_pt
    have := S_cross.isLocallyFinite j
    have h2 : ((S_cross.μS j) (tsupport _)).toReal ≤ M_K :=
      (ENNReal.toReal_mono (isCompact_Icc (a := -(R + 1)) (b := airyZero 1 + 2)).measure_lt_top.ne
        (measure_mono htsub)).trans hMK_j
    calc |∫ u, _ ∂(S_cross.μS j)| ≤ δ_end * ((S_cross.μS j) (tsupport _)).toReal := h1
      _ ≤ δ_end * M_K := mul_le_mul_of_nonneg_left h2 hδ_end.le
      _ ≤ δ_end * M_K' := by gcongr; dsimp [M_K']; linarith [le_max_left M_K 0]
      _ = ε / 6 := by dsimp [δ_end]; field_simp [hMK'_pos.ne']
  have htail_j : |∫ r in Ici (0 : ℝ), (1 - cutoff (-R) (airyZero 1 + 1) (uAiry (c' j) r)) *
        spinVolterraAdjoint g₅ r ∂ν₀| / S_scale ≤ ε / 6 + ε / 6 := by
    have ht_le := noncutoff_volterra_tail_le hc'0 ha_vir (hτ j) hCmid hSg0 hR_Sg hδ_noesc.le
      (by linarith : (0 : ℝ) ≤ ε / 6) (meas j) hgap_j g₅
      (bumpG virasoroProblem (rpParams 0).bumpData 1 (1 / 4) (designSigma1 0) (c' j))
      (T₁.Ψ j) hg5_int (T₁.continuous j) (funext hT1_j)
      (fun u hu => T₁.nonneg j u (hu.trans hθ_j)) (T₁.integrable_mu j) hmid_j hnoesc_j hfar_j.le
    refine ht_le.trans_eq ?_
    dsimp [δ_noesc]; field_simp [hCmid.ne']
  have hvag_d : |∫ u, cutoff (-R) (airyZero 1 + 1) u * ((xiStar ^ 3 / (3 * π)) * D.W u) ∂(S_cross.μS j) -
      ∫ u, cutoff (-R) (airyZero 1 + 1) u * ((xiStar ^ 3 / (3 * π)) * D.W u) ∂airyMeasure| ≤ ε / 6 := by
    rw [← Real.dist_eq]; exact (Metric.mem_ball.mp hvag_j).le
  rw [Real.dist_eq, hχ_split, add_div, hχ_spec]
  calc |(∫ u, cutoff (-R) (airyZero 1 + 1) u * (psiScale virasoroProblem (c' j) *
            psiAiry virasoroProblem (c' j) (spinMomentVolterraScaled d5 N η σs (c' j)) u) ∂(S_cross.μS j) +
          (∫ r in Ici 0, (1 - cutoff (-R) (airyZero 1 + 1) (uAiry (c' j) r)) *
            spinVolterraAdjoint g₅ r ∂ν₀) / S_scale) -
        (xiStar ^ 3 / (3 * π)) * D.V|
      ≤ |∫ u, cutoff (-R) (airyZero 1 + 1) u * (psiScale virasoroProblem (c' j) *
            psiAiry virasoroProblem (c' j) (spinMomentVolterraScaled d5 N η σs (c' j)) u) ∂(S_cross.μS j) -
          (xiStar ^ 3 / (3 * π)) * D.V| +
        |(∫ r in Ici 0, (1 - cutoff (-R) (airyZero 1 + 1) (uAiry (c' j) r)) *
          spinVolterraAdjoint g₅ r ∂ν₀) / S_scale| := by
        rw [add_sub_right_comm]; exact abs_add_le _ _
    _ ≤ (|∫ u, cutoff (-R) (airyZero 1 + 1) u * (psiScale virasoroProblem (c' j) *
              psiAiry virasoroProblem (c' j) (spinMomentVolterraScaled d5 N η σs (c' j)) u)
            ∂(S_cross.μS j) -
          ∫ u, cutoff (-R) (airyZero 1 + 1) u * ((xiStar ^ 3 / (3 * π)) * D.W u)
            ∂(S_cross.μS j)| +
          (|∫ u, cutoff (-R) (airyZero 1 + 1) u * ((xiStar ^ 3 / (3 * π)) * D.W u)
              ∂(S_cross.μS j) -
            ∫ u, cutoff (-R) (airyZero 1 + 1) u * ((xiStar ^ 3 / (3 * π)) * D.W u) ∂airyMeasure| +
            |∫ u, cutoff (-R) (airyZero 1 + 1) u * ((xiStar ^ 3 / (3 * π)) * D.W u) ∂airyMeasure -
              (xiStar ^ 3 / (3 * π)) * D.V|)) +
          |∫ r in Ici 0, (1 - cutoff (-R) (airyZero 1 + 1) (uAiry (c' j) r)) *
            spinVolterraAdjoint g₅ r ∂ν₀| / S_scale := by
        rw [abs_div, abs_of_pos hSs_pos]
        gcongr
        set I₁ := ∫ u, cutoff (-R) (airyZero 1 + 1) u * (psiScale virasoroProblem (c' j) *
            psiAiry virasoroProblem (c' j) (spinMomentVolterraScaled d5 N η σs (c' j)) u)
            ∂(S_cross.μS j)
        set I₂ := ∫ u, cutoff (-R) (airyZero 1 + 1) u * ((xiStar ^ 3 / (3 * π)) * D.W u)
            ∂(S_cross.μS j)
        set I₃ := ∫ u, cutoff (-R) (airyZero 1 + 1) u * ((xiStar ^ 3 / (3 * π)) * D.W u)
            ∂airyMeasure
        calc |I₁ - (xiStar ^ 3 / (3 * π)) * D.V|
            = |(I₁ - I₂) + ((I₂ - I₃) + (I₃ - (xiStar ^ 3 / (3 * π)) * D.V))| := by
              congr 1; ring
          _ ≤ |I₁ - I₂| + |(I₂ - I₃) + (I₃ - (xiStar ^ 3 / (3 * π)) * D.V)| :=
              abs_add_le (I₁ - I₂) _
          _ ≤ |I₁ - I₂| + (|I₂ - I₃| + |I₃ - (xiStar ^ 3 / (3 * π)) * D.V|) :=
              add_le_add le_rfl (abs_add_le (I₂ - I₃) _)
    _ ≤ (ε / 6 + (ε / 6 + ε / 6)) + (ε / 6 + ε / 6) := add_le_add
        (add_le_add hend_diff (add_le_add hvag_d hR_Ai')) htail_j
    _ < ε := by linarith

/-- info: 'FormalResearch.ModularBootstrap.Spin.spinMoment_volterra_source_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms spinMoment_volterra_source_tendsto

/-- **`sd:spinmoment-window-pair`**: integrability and upper limsup bound for the weight-5
bumped test against the spin second-moment spectral measure `μM_j`. -/
theorem spinMoment_window_pair_limsup_le (N : ℕ) (hN : 1 ≤ N) {η : ℝ} (hη0 : 0 < η)
    (hη1 : η ≤ 1 / 4) (σs : ℕ → ℝ) (D : Window) (hW : D.W = sigWinW N η σs)
    (cSeq τSeq BSeq : ℕ → ℝ) (hc : Tendsto cSeq atTop atTop)
    (hc25 : ∀ j, 25 ≤ cSeq j) (hτ : ∀ j, 0 < τSeq j) (hB : ∀ j, 0 ≤ BSeq j)
    (hGap : GapCondition (fun j => cSeq j - 1) τSeq)
    (meas : ∀ j, SpinCrossingMeasureOn ((cSeq j - 1) / 12)
      (spinConeB (BSeq j) ∩ {p | τSeq j ≤ p.1 + p.2}))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ j in atTop,
      Integrable (fun u => psiScale virasoroProblem (cSeq j - 1) *
          psiAiry virasoroProblem (cSeq j - 1)
            (bumpG spinMomentW5Prob (rpParams 4).bumpData N η σs (cSeq j - 1)) u)
        (spinMomentSpectralMeasure (cSeq j - 1) (meas j).ν) ∧
      ∫ u, psiScale virasoroProblem (cSeq j - 1) *
          psiAiry virasoroProblem (cSeq j - 1)
            (bumpG spinMomentW5Prob (rpParams 4).bumpData N η σs (cSeq j - 1)) u
        ∂(spinMomentSpectralMeasure (cSeq j - 1) (meas j).ν) ≤ spinMomentVStar * D.V + ε := by
  let c' : ℕ → ℝ := fun j => cSeq j - 1
  have hc' : Tendsto c' atTop atTop := by
    have : c' = fun j => cSeq j + (-1) := by ext j; ring
    rw [this]; exact hc.atTop_add tendsto_const_nhds
  set d5 := (rpParams 4).bumpData
  have hgood := hc'.eventually (bumpG_good spinMomentW5Prob d5 N hN hη0.le hη1 σs)
  have hvac := hc'.eventually (spinMoment_vac_source_limsup_le N hN hη0 hη1 σs (ε / 2) (half_pos hε))
  have hvolt := (spinMoment_volterra_source_tendsto N hN hη0 hη1 σs D hW cSeq τSeq BSeq
    hc hc25 hτ hB hGap meas).eventually (ge_mem_nhds (by linarith : (xiStar ^ 3 / (3 * π)) * D.V <
      (xiStar ^ 3 / (3 * π)) * D.V + ε / 2))
  filter_upwards [hgood, hvac, hvolt] with j hgj hvacj hvoltj
  obtain ⟨hc'0, htest5, C_g, hCg_nn, hdec5⟩ := hgj
  have hc24 : 24 ≤ c' j := by dsimp [c']; linarith [hc25 j]
  have ha2 : (2 : ℝ) ≤ c' j / 12 := by linarith
  have hdec5' : ∀ t : ℝ, 0 ≤ t → |bumpG spinMomentW5Prob d5 N η σs (c' j) t| ≤
      C_g * Real.exp (-4 * π * Real.sqrt (c' j / 12 * t) - (π * Real.sqrt (3 / c' j)) * Real.sqrt t) := by
    intro t ht
    have hsq : Real.sqrt (3 * t / c' j) = Real.sqrt (3 / c' j) * Real.sqrt t := by
      rw [show 3 * t / c' j = (3 / c' j) * t by ring, Real.sqrt_mul (by positivity)]
    rw [mul_assoc π, ← hsq]; exact hdec5 t ht
  have hpair := spinMoment_pair ha2 (hB j) (hτ j) (fun _ hp => hp) (meas j) htest5
    (by positivity : 0 < π * Real.sqrt (3 / c' j)) hCg_nn hdec5'
  have hint_mu : Integrable (fun u => psiScale virasoroProblem (c' j) *
      psiAiry virasoroProblem (c' j) (bumpG spinMomentW5Prob d5 N η σs (c' j)) u)
      (spinMomentSpectralMeasure (c' j) (meas j).ν) :=
    ((integrable_spinMomentSpectralMeasure_psiAiry_iff hc24 (hτ j)
      (fun _ (hp : _ ∈ spinConeB (BSeq j) ∩ {p | τSeq j ≤ p.1 + p.2}) => hp.2)
      (meas j) htest5.cont).mpr hpair.1).const_mul _
  refine ⟨hint_mu, ?_⟩
  rw [integral_const_mul, integral_spinMomentSpectralMeasure_psiAiry hc24 (hτ j)
    (fun _ (hp : _ ∈ spinConeB (BSeq j) ∩ {p | τSeq j ≤ p.1 + p.2}) => hp.2)
    (meas j) htest5.cont]
  have hsplit := hpair.2.2.2
  have hid_scale : psiScale virasoroProblem (c' j) *
      ((∫ t in Ici 0, bumpG spinMomentW5Prob d5 N η σs (c' j) t ∂spinMomentMeasure (meas j).ν) /
        (2 * π * c' j)) =
      (∫ t in Ici 0, bumpG spinMomentW5Prob d5 N η σs (c' j) t * spinVacHC (c' j / 12) t) /
        (π * c' j * CStar * FKc 1 1 (c' j)) +
      (∫ r in Ici 0, spinVolterraAdjoint (bumpG spinMomentW5Prob d5 N η σs (c' j)) r
        ∂spinRadMarginal (meas j).ν) / (π * c' j * CStar * FKc 1 1 (c' j)) := by
    rw [hsplit]
    unfold psiScale
    rw [qProb_virasoro]
    have hpi := Real.pi_pos; have hCS := CStar_pos; have hFK := FKc_pos zero_lt_one 1 hc'0
    field_simp
  rw [hid_scale, MeasureTheory.integral_Ici_eq_integral_Ioi]
  have hvac_le : (∫ t in Ioi 0, bumpG spinMomentW5Prob d5 N η σs (c' j) t * spinVacHC (c' j / 12) t) /
      (π * c' j * CStar * FKc 1 1 (c' j)) ≤ (xiStar ^ 3 / (3 * π)) * D.V + ε / 2 := by
    rw [← windowIntegralSig_eq_windowV N η σs D hW]
    exact hvacj.2
  have hvolt_le : (∫ r in Ici 0, spinVolterraAdjoint (bumpG spinMomentW5Prob d5 N η σs (c' j)) r
      ∂spinRadMarginal (meas j).ν) / (π * c' j * CStar * FKc 1 1 (c' j)) ≤
      (xiStar ^ 3 / (3 * π)) * D.V + ε / 2 := hvoltj
  calc _ ≤ ((xiStar ^ 3 / (3 * π)) * D.V + ε / 2) + ((xiStar ^ 3 / (3 * π)) * D.V + ε / 2) :=
        add_le_add hvac_le hvolt_le
    _ = spinMomentVStar * D.V + ε := by unfold spinMomentVStar; ring

/-- info: 'FormalResearch.ModularBootstrap.Spin.spinMoment_window_pair_limsup_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms spinMoment_window_pair_limsup_le

end FormalResearch.ModularBootstrap.Spin
