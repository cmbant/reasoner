module

public import FormalResearch.ModularBootstrap.FoldTip.ChartCompactness
public import FormalResearch.ModularBootstrap.FoldTip.Instances
public import FormalResearch.ModularBootstrap.Blowup.NormLimitConcrete
public import FormalResearch.SignUncertainty.RadialRigidity

/-!
# Fixed-Weight Fold-Tip Chart Compactness (`FT-CC` Paper II Instances)

Instantiates `ChartCompactness` (`FoldTip/ChartCompactness.lean`) for Paper II's fixed-weight
modular bootstrap (`FoldTipSetting.ofFixedWeight prob`, any `prob : FixedWeightProblem`, at any
Hermite–Biehler level `H : HermiteBiehlerData`: `HermiteBiehlerData.airy`,
`HermiteBiehlerData.clark hα`, or any `AiryPQHB`).

Following `ft:L2` (iii) (`fold_tip_universality.tex`), `fwExtPsi` extends the chart-transported
density `psiTilde` outside `[-A_c², A_c²]` by pushing forward the physical density along the
piecewise-linear extension of `virasoroDeltaChart` (extended by `0` beyond `A_c² + Δ(A_c²)`),
so that `∫ |ψ n| = 1`, `∫ ψ n ≤ 0` and `ψ n ≥ 0` on `(-∞, fwExtUT n]` hold identically.

## Main results
- `fixedWeight_chartCompactness`: instantiates `ChartCompactness ℕ atTop H` for any
  `prob : FixedWeightProblem`, `H : HermiteBiehlerData`, and sequence of weakly feasible tests
  at `c' n → ∞` with prescribed-node nonnegativity `0 ≤ g n (Δ_{c' n}(uSite t n))`.
- `fixedWeight_chartCompactness_virasoro`, `fixedWeight_chartCompactness_clark`:
  specializations to `virasoroProblem` / `HermiteBiehlerData.airy` and `HermiteBiehlerData.clark`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.FoldTip

open FormalResearch.SignUncertainty
open FormalResearch.Special
open FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.FixedWeightTip
open FormalResearch.ModularBootstrap.ConcreteBootstrap
open FormalResearch.ModularBootstrap.Blowup

/-! ### Piecewise-linear extended chart density and threshold -/

/-- Extended chart density on `ℝ` (`ft:L2` (iii)): agrees with `Re (psiTilde prob c' g)`
(and hence with `fwChart.PsiT (FoldTipSetting.ofFixedWeight prob) c' g`) on `[-A², A²]`,
pushes forward the physical density linearly on `(-∞, -A²)` and `(A², A² + Δ(A²))`,
and vanishes on `[A² + Δ(A²), ∞)`. -/
noncomputable def fwExtPsi (prob : FixedWeightProblem) (c' A : ℝ) (g : ℝ → ℝ) (u : ℝ) : ℝ :=
  let Δ_pos := virasoroDeltaChart c' (A ^ 2)
  let Δ_neg := virasoroDeltaChart c' (-(A ^ 2))
  if |u| ≤ A ^ 2 then (psiTilde prob c' g (u : ℂ)).re
  else if u < -(A ^ 2) then
    (prob.cardyNorm (c' / 12) g)⁻¹ *
      (g (Δ_neg + (-(A ^ 2) - u)) * prob.cardyV (c' / 12) (Δ_neg + (-(A ^ 2) - u)))
  else if u < A ^ 2 + Δ_pos then
    (prob.cardyNorm (c' / 12) g)⁻¹ *
      (g (Δ_pos - (u - A ^ 2)) * prob.cardyV (c' / 12) (Δ_pos - (u - A ^ 2)))
  else 0

/-- Extended chart threshold matching `fwExtPsi`: agrees with `chartUT c' T` whenever
`Δ(A²) ≤ T ≤ Δ(-A²)`, and extends linearly outside. -/
noncomputable def fwExtUT (c' A T : ℝ) : ℝ :=
  let Δ_pos := virasoroDeltaChart c' (A ^ 2)
  let Δ_neg := virasoroDeltaChart c' (-(A ^ 2))
  if T < Δ_pos then A ^ 2 + (Δ_pos - T)
  else if T ≤ Δ_neg then chartUT c' T
  else -(A ^ 2) - (T - Δ_neg)

private lemma fwExtUT_lt {c' A T : ℝ} (h : T < virasoroDeltaChart c' (A ^ 2)) :
    fwExtUT c' A T = A ^ 2 + (virasoroDeltaChart c' (A ^ 2) - T) := by
  dsimp only [fwExtUT]
  split_ifs
  rfl

private lemma fwExtUT_mid {c' A T : ℝ} (h1 : virasoroDeltaChart c' (A ^ 2) ≤ T)
    (h2 : T ≤ virasoroDeltaChart c' (-(A ^ 2))) :
    fwExtUT c' A T = chartUT c' T := by
  dsimp only [fwExtUT]
  split_ifs with h1'
  · exact absurd h1' (not_lt.mpr h1)
  · rfl

private lemma fwExtUT_gt {c' A T : ℝ} (h1 : virasoroDeltaChart c' (A ^ 2) ≤ T)
    (h2 : virasoroDeltaChart c' (-(A ^ 2)) < T) :
    fwExtUT c' A T = -(A ^ 2) - (T - virasoroDeltaChart c' (-(A ^ 2))) := by
  dsimp only [fwExtUT]
  split_ifs with h1' h2'
  · exact absurd h1' (not_lt.mpr h1)
  · exact absurd h2' (not_le.mpr h2)
  · rfl

/-! ### Integrability, mass, and sign properties of `fwExtPsi` -/

private lemma fwExtPsi_eq_psiTilde {prob : FixedWeightProblem} {c' A : ℝ} {g : ℝ → ℝ}
    {u : ℝ} (hu : |u| ≤ A ^ 2) :
    fwExtPsi prob c' A g u = (psiTilde prob c' g (u : ℂ)).re := by
  unfold fwExtPsi; simp [hu]

private lemma fwExtPsi_left {prob : FixedWeightProblem} {c' A : ℝ} {g : ℝ → ℝ}
    {u : ℝ} (hu : u < -(A ^ 2)) :
    fwExtPsi prob c' A g u =
      (prob.cardyNorm (c' / 12) g)⁻¹ *
        (g (virasoroDeltaChart c' (-(A ^ 2)) + (-(A ^ 2) - u)) *
          prob.cardyV (c' / 12) (virasoroDeltaChart c' (-(A ^ 2)) + (-(A ^ 2) - u))) := by
  have hnot : ¬ |u| ≤ A ^ 2 := by
    rw [abs_le]; push Not; exact fun h => absurd (lt_of_le_of_lt h hu) (lt_irrefl _)
  unfold fwExtPsi
  simp only [hnot, ↓reduceIte, hu]

private lemma fwExtPsi_mid_right {prob : FixedWeightProblem} {c' A : ℝ} {g : ℝ → ℝ}
    {u : ℝ} (hA0 : 0 ≤ A ^ 2) (hu1 : A ^ 2 < u)
    (hu2 : u < A ^ 2 + virasoroDeltaChart c' (A ^ 2)) :
    fwExtPsi prob c' A g u =
      (prob.cardyNorm (c' / 12) g)⁻¹ *
        (g (virasoroDeltaChart c' (A ^ 2) - (u - A ^ 2)) *
          prob.cardyV (c' / 12) (virasoroDeltaChart c' (A ^ 2) - (u - A ^ 2))) := by
  have hnot1 : ¬ |u| ≤ A ^ 2 := by
    rw [abs_le]; push Not; intro _; exact hu1
  have hnot2 : ¬ u < -(A ^ 2) := by linarith
  unfold fwExtPsi
  simp only [hnot1, ↓reduceIte, hnot2, hu2]

private lemma fwExtPsi_far_right {prob : FixedWeightProblem} {c' A : ℝ} {g : ℝ → ℝ}
    {u : ℝ} (hA0 : 0 ≤ A ^ 2) (hu : A ^ 2 + virasoroDeltaChart c' (A ^ 2) ≤ u)
    (hΔ : 0 < virasoroDeltaChart c' (A ^ 2)) :
    fwExtPsi prob c' A g u = 0 := by
  have hnot1 : ¬ |u| ≤ A ^ 2 := by
    rw [abs_le]; push Not; intro _; linarith
  have hnot2 : ¬ u < -(A ^ 2) := by linarith
  have hnot3 : ¬ u < A ^ 2 + virasoroDeltaChart c' (A ^ 2) := not_lt.mpr hu
  unfold fwExtPsi
  simp only [hnot1, ↓reduceIte, hnot2, hnot3]

private lemma integrableOn_gV_Ioi {prob : FixedWeightProblem} {c' : ℝ}
    (_hV_nn : ∀ t : ℝ, 0 ≤ t → 0 ≤ prob.cardyV (c' / 12) t)
    {g : ℝ → ℝ} (hg : TestClass prob (c' / 12) g) :
    IntegrableOn (fun t => g t * prob.cardyV (c' / 12) t) (Ioi 0) := by
  refine hg.int_cardy.norm.mono'
    (((hg.cont.mul (continuous_cardyV prob (c' / 12)).continuousOn).mono
      Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi)
    (Eventually.of_forall fun t => ?_)
  simp [Real.norm_eq_abs]

private lemma fwExtPsi_integrals {prob : FixedWeightProblem} (D : UniformPropositionPData prob)
    {c' : ℝ} (hc' : D.c₀ ≤ c') {g : ℝ → ℝ} (hg : TestClass prob (c' / 12) g)
    (hM_pos : 0 < prob.cardyNorm (c' / 12) g)
    (han : AnalyticOnNhd ℂ (psiTilde prob c' g) (psiDom c')) :
    let A := chartAC D.r_1 c'
    Integrable (fwExtPsi prob c' A g) ∧
    (∫ u : ℝ, |fwExtPsi prob c' A g u| = 1) ∧
    (∫ u : ℝ, fwExtPsi prob c' A g u =
      (prob.cardyNorm (c' / 12) g)⁻¹ * ∫ t in Ioi (0 : ℝ), g t * prob.cardyV (c' / 12) t) ∧
    (∀ R : ℝ, 0 ≤ R → R ≤ A ^ 2 →
      ∫ u in Ioi R, |fwExtPsi prob c' A g u| =
        (∫ u in R..(A ^ 2), ‖psiTilde prob c' g (u : ℂ)‖) + deltaLobe prob D.r_1 c' g) := by
  intro A
  have hc'_pos : 0 < c' := D.hc₀_pos.trans_le hc'
  have hA2_nn : 0 ≤ A ^ 2 := sq_nonneg _
  have hA2_vir : A ^ 2 ≤ virasoroAC c' ^ 2 := chartAC_sq_le_virasoroAC_sq D.hr1_pos hc'_pos.le
  have hΔpos : 0 < virasoroDeltaChart c' (A ^ 2) :=
    virasoroDeltaChart_pos hc'_pos (chart_real_abs_le_virasoro D.hr1_pos hc'_pos
      (by rw [abs_of_nonneg hA2_nn]))
  have hΔ_lt : virasoroDeltaChart c' (A ^ 2) < virasoroDeltaChart c' (-(A ^ 2)) := by
    by_cases hA0 : A ^ 2 = 0
    · exfalso
      have hposA : 0 < A ^ 2 := by
        rw [chartAC_sq D.r_1 c' hc'_pos.le]
        exact mul_pos (mul_pos two_pos (pow_pos (chartBV_pos D.hr1_pos) 2))
          (Real.rpow_pos_of_pos hc'_pos _)
      linarith
    · have hposA : 0 < A ^ 2 := lt_of_le_of_ne hA2_nn (Ne.symm hA0)
      exact (virasoroDeltaChart_strictAnti hc'_pos)
        ⟨by linarith, by linarith⟩ ⟨by linarith, hA2_vir⟩ (by linarith)
  set Δp := virasoroDeltaChart c' (A ^ 2) with hΔp_def
  set Δn := virasoroDeltaChart c' (-(A ^ 2)) with hΔn_def
  have hV_nn : ∀ t : ℝ, 0 ≤ t → 0 ≤ prob.cardyV (c' / 12) t := fun t ht =>
    D.cardyV_nonneg hc' ht
  have hgv_int : IntegrableOn (fun t => g t * prob.cardyV (c' / 12) t) (Ioi 0) :=
    integrableOn_gV_Ioi hV_nn hg
  have hgv_abs_int : IntegrableOn (fun t => |g t| * prob.cardyV (c' / 12) t) (Ioi 0) :=
    hg.int_cardy
  let f_raw : ℝ → ℝ := fun t => (prob.cardyNorm (c' / 12) g)⁻¹ * (g t * prob.cardyV (c' / 12) t)
  have hf_raw_int : IntegrableOn f_raw (Ioi 0) := hgv_int.const_mul _
  have hf_raw_abs_int : IntegrableOn (fun t => |f_raw t|) (Ioi 0) := by
    have hmul : IntegrableOn (fun t => (prob.cardyNorm (c' / 12) g)⁻¹ * (|g t| * prob.cardyV (c' / 12) t)) (Ioi 0) :=
      hgv_abs_int.const_mul (prob.cardyNorm (c' / 12) g)⁻¹
    refine hmul.congr_fun ?_ measurableSet_Ioi
    intro t ht
    dsimp [f_raw]
    rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr hM_pos.le), abs_mul,
      abs_of_nonneg (hV_nn t (mem_Ioi.mp ht).le)]
  -- Helper: reflection change of variables `u ↦ c - u`
  have sub_preimage_int : ∀ (c : ℝ) (h : ℝ → ℝ) (s : Set ℝ),
      MeasurableSet s → IntegrableOn h s →
      IntegrableOn (fun u => h (c - u)) ((fun u => c - u) ⁻¹' s) ∧
        ∫ u in (fun u => c - u) ⁻¹' s, h (c - u) = ∫ t in s, h t := by
    intro c h s _ hs_int
    let e : ℝ ≃ᵐ ℝ :=
      { toEquiv :=
          ⟨fun x => c - x, fun x => c - x, fun _ => sub_sub_cancel _ _, fun _ => sub_sub_cancel _ _⟩
        measurable_toFun := measurable_const.sub measurable_id
        measurable_invFun := measurable_const.sub measurable_id }
    have hmp : MeasurePreserving e volume volume := Measure.measurePreserving_sub_left volume c
    exact ⟨(hmp.integrableOn_comp_preimage e.measurableEmbedding).mpr hs_int,
      hmp.setIntegral_preimage_emb e.measurableEmbedding h s⟩
  -- Piece 1: `Iio (-A²)` via `u ↦ (Δn - A²) - u`
  have hpre1 : (fun u : ℝ => (Δn - A ^ 2) - u) ⁻¹' Ioi Δn = Iio (-(A ^ 2)) := by
    ext u; simp only [mem_preimage, mem_Ioi, mem_Iio]; constructor <;> intro h <;> linarith
  have heq1_fun : ∀ u, f_raw (Δn + (-(A ^ 2) - u)) = f_raw ((Δn - A ^ 2) - u) := by
    intro u; ring_nf
  have h1_pair := sub_preimage_int (Δn - A ^ 2) f_raw (Ioi Δn) measurableSet_Ioi
    (hf_raw_int.mono_set (Ioi_subset_Ioi (hΔpos.trans hΔ_lt).le))
  have h1_abs_pair := sub_preimage_int (Δn - A ^ 2) (fun t => |f_raw t|) (Ioi Δn) measurableSet_Ioi
    (hf_raw_abs_int.mono_set (Ioi_subset_Ioi (hΔpos.trans hΔ_lt).le))
  rw [hpre1] at h1_pair h1_abs_pair
  have hI_left_int : IntegrableOn (fwExtPsi prob c' A g) (Iio (-(A ^ 2))) :=
    h1_pair.1.congr_fun (fun u hu => by rw [fwExtPsi_left hu, ← hΔn_def]; exact (heq1_fun u).symm) measurableSet_Iio
  have hI_left_abs_int : IntegrableOn (fun u => |fwExtPsi prob c' A g u|) (Iio (-(A ^ 2))) :=
    h1_abs_pair.1.congr_fun
      (fun u hu => by rw [fwExtPsi_left hu, ← hΔn_def]; exact congrArg abs (heq1_fun u).symm) measurableSet_Iio
  have hI_left_eq : ∫ u in Iio (-(A ^ 2)), fwExtPsi prob c' A g u = ∫ t in Ioi Δn, f_raw t := by
    calc ∫ u in Iio (-(A ^ 2)), fwExtPsi prob c' A g u
        = ∫ u in Iio (-(A ^ 2)), f_raw ((Δn - A ^ 2) - u) :=
            setIntegral_congr_fun measurableSet_Iio
              fun u hu => by rw [fwExtPsi_left hu, ← hΔn_def]; exact heq1_fun u
      _ = ∫ t in Ioi Δn, f_raw t := h1_pair.2
  have hI_left_abs_eq : ∫ u in Iio (-(A ^ 2)), |fwExtPsi prob c' A g u| =
      ∫ t in Ioi Δn, |f_raw t| := by
    calc ∫ u in Iio (-(A ^ 2)), |fwExtPsi prob c' A g u|
        = ∫ u in Iio (-(A ^ 2)), |f_raw ((Δn - A ^ 2) - u)| :=
            setIntegral_congr_fun measurableSet_Iio
              fun u hu => by rw [fwExtPsi_left hu, ← hΔn_def]; exact congrArg abs (heq1_fun u)
      _ = ∫ t in Ioi Δn, |f_raw t| := h1_abs_pair.2
  -- Piece 3: `Ioo (A²) (A² + Δp)` via `u ↦ (A² + Δp) - u`
  have hpre3 : (fun u : ℝ => (A ^ 2 + Δp) - u) ⁻¹' Ioo 0 Δp = Ioo (A ^ 2) (A ^ 2 + Δp) := by
    ext u; simp only [mem_preimage, mem_Ioo]; constructor <;> intro h <;> exact ⟨by linarith, by linarith⟩
  have heq3_fun : ∀ u, f_raw (Δp - (u - A ^ 2)) = f_raw ((A ^ 2 + Δp) - u) := by
    intro u; ring_nf
  have h3_pair := sub_preimage_int (A ^ 2 + Δp) f_raw (Ioo 0 Δp) measurableSet_Ioo
    (hf_raw_int.mono_set Ioo_subset_Ioi_self)
  have h3_abs_pair := sub_preimage_int (A ^ 2 + Δp) (fun t => |f_raw t|) (Ioo 0 Δp) measurableSet_Ioo
    (hf_raw_abs_int.mono_set Ioo_subset_Ioi_self)
  rw [hpre3] at h3_pair h3_abs_pair
  have hI_midR_int : IntegrableOn (fwExtPsi prob c' A g) (Ioo (A ^ 2) (A ^ 2 + Δp)) :=
    h3_pair.1.congr_fun
      (fun u hu => by rw [fwExtPsi_mid_right hA2_nn hu.1 hu.2, ← hΔp_def]; exact (heq3_fun u).symm) measurableSet_Ioo
  have hI_midR_abs_int :
      IntegrableOn (fun u => |fwExtPsi prob c' A g u|) (Ioo (A ^ 2) (A ^ 2 + Δp)) :=
    h3_abs_pair.1.congr_fun
      (fun u hu => by rw [fwExtPsi_mid_right hA2_nn hu.1 hu.2, ← hΔp_def]; exact congrArg abs (heq3_fun u).symm) measurableSet_Ioo
  have hIoo_Ioc_raw : ∫ t in Ioo 0 Δp, f_raw t = ∫ t in Ioc 0 Δp, f_raw t :=
    setIntegral_congr_set Ioo_ae_eq_Ioc
  have hIoo_Ioc_abs : ∫ t in Ioo 0 Δp, |f_raw t| = ∫ t in Ioc 0 Δp, |f_raw t| :=
    setIntegral_congr_set Ioo_ae_eq_Ioc
  have hI_midR_eq : ∫ u in Ioo (A ^ 2) (A ^ 2 + Δp), fwExtPsi prob c' A g u =
      ∫ t in Ioc 0 Δp, f_raw t := by
    calc ∫ u in Ioo (A ^ 2) (A ^ 2 + Δp), fwExtPsi prob c' A g u
        = ∫ u in Ioo (A ^ 2) (A ^ 2 + Δp), f_raw ((A ^ 2 + Δp) - u) :=
            setIntegral_congr_fun measurableSet_Ioo
              fun u hu => by rw [fwExtPsi_mid_right hA2_nn hu.1 hu.2, ← hΔp_def]; exact heq3_fun u
      _ = ∫ t in Ioo 0 Δp, f_raw t := h3_pair.2
      _ = ∫ t in Ioc 0 Δp, f_raw t := hIoo_Ioc_raw
  have hI_midR_abs_eq : ∫ u in Ioo (A ^ 2) (A ^ 2 + Δp), |fwExtPsi prob c' A g u| =
      ∫ t in Ioc 0 Δp, |f_raw t| := by
    calc ∫ u in Ioo (A ^ 2) (A ^ 2 + Δp), |fwExtPsi prob c' A g u|
        = ∫ u in Ioo (A ^ 2) (A ^ 2 + Δp), |f_raw ((A ^ 2 + Δp) - u)| :=
            setIntegral_congr_fun measurableSet_Ioo
              fun u hu => by rw [fwExtPsi_mid_right hA2_nn hu.1 hu.2, ← hΔp_def]; exact congrArg abs (heq3_fun u)
      _ = ∫ t in Ioo 0 Δp, |f_raw t| := h3_abs_pair.2
      _ = ∫ t in Ioc 0 Δp, |f_raw t| := hIoo_Ioc_abs
  -- Piece 2: `Icc (-A²) (A²)` via `psiTilde`
  have hpsi_cont_vir : ContinuousOn (fun u : ℝ => psiTilde prob c' g (u : ℂ))
      (Icc (-(A ^ 2)) (A ^ 2)) := by
    refine (han.continuousOn.mono (closedBall_chartAC_subset_psiDom D.hr1_pos hc'_pos)).comp
      continuous_ofReal.continuousOn fun u hu => ?_
    rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]
    exact abs_le.mpr hu
  have hI_mid_int : IntegrableOn (fwExtPsi prob c' A g) (Icc (-(A ^ 2)) (A ^ 2)) := by
    have hcont : ContinuousOn (fun u : ℝ => (psiTilde prob c' g (u : ℂ)).re)
        (Icc (-(A ^ 2)) (A ^ 2)) :=
      Complex.continuous_re.comp_continuousOn hpsi_cont_vir
    exact hcont.integrableOn_Icc.congr_fun
      (fun u hu => (fwExtPsi_eq_psiTilde (abs_le.mpr hu)).symm) measurableSet_Icc
  have hI_mid_abs_int :
      IntegrableOn (fun u => |fwExtPsi prob c' A g u|) (Icc (-(A ^ 2)) (A ^ 2)) :=
    hI_mid_int.norm
  have hI_mid_eq : ∫ u in Icc (-(A ^ 2)) (A ^ 2), fwExtPsi prob c' A g u =
      ∫ t in Ioc Δp Δn, f_raw t := by
    have hre : ∫ u in Icc (-(A ^ 2)) (A ^ 2), fwExtPsi prob c' A g u =
        ∫ u in (-(A ^ 2))..(A ^ 2), (psiTilde prob c' g (u : ℂ)).re := by
      rw [setIntegral_congr_fun measurableSet_Icc (fun u hu => fwExtPsi_eq_psiTilde (abs_le.mpr hu)),
        ← setIntegral_congr_set Ioc_ae_eq_Icc,
        ← intervalIntegral.integral_of_le (by linarith : -(A ^ 2) ≤ A ^ 2)]
    rw [hre, psiTilde_re_integral_eq prob hc'_pos hg (by linarith [hA2_vir]) hA2_vir (by linarith),
      intervalIntegral.integral_of_le hΔ_lt.le, ← integral_const_mul]
  have hI_mid_abs_eq : ∫ u in Icc (-(A ^ 2)) (A ^ 2), |fwExtPsi prob c' A g u| =
      ∫ t in Ioc Δp Δn, |f_raw t| := by
    have hnorm1 : ∫ u in Icc (-(A ^ 2)) (A ^ 2), |fwExtPsi prob c' A g u| =
        ∫ u in Icc (-(A ^ 2)) (A ^ 2), ‖psiTilde prob c' g (u : ℂ)‖ := by
      refine setIntegral_congr_fun measurableSet_Icc fun u hu => ?_
      have hu_abs := abs_le.mpr hu
      rw [fwExtPsi_eq_psiTilde hu_abs]
      have him := psiTilde_im_ofReal prob hc'_pos hg (hu_abs.trans hA2_vir)
      rw [Complex.norm_def, Complex.normSq_apply, him, mul_zero, add_zero, ← sq, Real.sqrt_sq_eq_abs]
    have hnorm : ∫ u in Icc (-(A ^ 2)) (A ^ 2), |fwExtPsi prob c' A g u| =
        ∫ u in (-(A ^ 2))..(A ^ 2), ‖psiTilde prob c' g (u : ℂ)‖ := by
      rw [hnorm1, ← setIntegral_congr_set Ioc_ae_eq_Icc,
        ← intervalIntegral.integral_of_le (by linarith : -(A ^ 2) ≤ A ^ 2)]
    rw [hnorm, psiTilde_norm_integral_eq prob hc'_pos (fun {t} ht => hV_nn t ht) hg hM_pos
      (by linarith [hA2_vir]) hA2_vir (by linarith), intervalIntegral.integral_of_le hΔ_lt.le,
      ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    dsimp [f_raw]
    rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr hM_pos.le), abs_mul,
      abs_of_nonneg (hV_nn t ((hΔpos.trans ht.1).le))]
  -- Piece 4: `Ici (A² + Δp)` is identically `0`
  have hI_far_int : IntegrableOn (fwExtPsi prob c' A g) (Ici (A ^ 2 + Δp)) :=
    (integrableOn_zero (μ := volume) (s := Ici (A ^ 2 + Δp))).congr_fun
      (fun u hu => (fwExtPsi_far_right hA2_nn hu hΔpos).symm) measurableSet_Ici
  have hI_far_abs_int :
      IntegrableOn (fun u => |fwExtPsi prob c' A g u|) (Ici (A ^ 2 + Δp)) :=
    (integrableOn_zero (μ := volume) (s := Ici (A ^ 2 + Δp))).congr_fun
      (fun u hu => by simp [fwExtPsi_far_right hA2_nn hu hΔpos]) measurableSet_Ici
  have hI_far_eq : ∫ u in Ici (A ^ 2 + Δp), fwExtPsi prob c' A g u = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero fun u hu => fwExtPsi_far_right hA2_nn hu hΔpos
  have hI_far_abs_eq : ∫ u in Ici (A ^ 2 + Δp), |fwExtPsi prob c' A g u| = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero fun u hu => by simp [fwExtPsi_far_right hA2_nn hu hΔpos]
  -- Combine all 4 pieces on `ℝ`
  have hu_12 : Disjoint (Iio (-(A ^ 2))) (Icc (-(A ^ 2)) (A ^ 2)) :=
    Set.disjoint_left.mpr fun _ hx1 hx2 => absurd hx1 (not_lt.mpr hx2.1)
  have hu_123 : Disjoint (Iio (-(A ^ 2)) ∪ Icc (-(A ^ 2)) (A ^ 2)) (Ioo (A ^ 2) (A ^ 2 + Δp)) :=
    Set.disjoint_left.mpr fun _ hx1 hx2 => by
      rcases hx1 with h1 | h2
      · linarith [mem_Iio.mp h1, hA2_nn, hx2.1]
      · exact absurd hx2.1 (not_lt.mpr h2.2)
  have hu_1234 : Disjoint ((Iio (-(A ^ 2)) ∪ Icc (-(A ^ 2)) (A ^ 2)) ∪ Ioo (A ^ 2) (A ^ 2 + Δp))
      (Ici (A ^ 2 + Δp)) :=
    Set.disjoint_left.mpr fun _ hx1 hx2 => by
      rcases hx1 with (h1 | h2) | h3
      · linarith [mem_Iio.mp h1, hA2_nn, hΔpos, mem_Ici.mp hx2]
      · linarith [h2.2, hΔpos, mem_Ici.mp hx2]
      · exact absurd h3.2 (not_lt.mpr hx2)
  have hunion_univ :
      ((Iio (-(A ^ 2)) ∪ Icc (-(A ^ 2)) (A ^ 2)) ∪ Ioo (A ^ 2) (A ^ 2 + Δp)) ∪ Ici (A ^ 2 + Δp) =
        univ := by
    ext u
    simp only [mem_union, mem_Iio, mem_Icc, mem_Ioo, mem_Ici, mem_univ, iff_true]
    rcases lt_or_ge u (-(A ^ 2)) with h1 | h1
    · exact Or.inl (Or.inl (Or.inl h1))
    · rcases le_or_gt u (A ^ 2) with h2 | h2
      · exact Or.inl (Or.inl (Or.inr ⟨h1, h2⟩))
      · rcases lt_or_ge u (A ^ 2 + Δp) with h3 | h3
        · exact Or.inl (Or.inr ⟨h2, h3⟩)
        · exact Or.inr h3
  have h_int_univ : IntegrableOn (fwExtPsi prob c' A g) univ := by
    rw [← hunion_univ]
    exact ((hI_left_int.union hI_mid_int).union hI_midR_int).union hI_far_int
  have h_abs_int_univ : IntegrableOn (fun u => |fwExtPsi prob c' A g u|) univ := by
    rw [← hunion_univ]
    exact ((hI_left_abs_int.union hI_mid_abs_int).union hI_midR_abs_int).union hI_far_abs_int
  have ht_disj1 : Disjoint (Ioc 0 Δp) (Ioc Δp Δn) :=
    Set.disjoint_left.mpr fun _ hx1 hx2 => absurd hx2.1 (not_lt.mpr hx1.2)
  have ht_disj2 : Disjoint (Ioc 0 Δp ∪ Ioc Δp Δn) (Ioi Δn) :=
    Set.disjoint_left.mpr fun _ hx1 hx2 => by
      rcases hx1 with h1 | h2
      · linarith [h1.2, hΔ_lt, mem_Ioi.mp hx2]
      · exact absurd hx2 (not_lt.mpr h2.2)
  have ht_union : (Ioc 0 Δp ∪ Ioc Δp Δn) ∪ Ioi Δn = Ioi 0 := by
    rw [Ioc_union_Ioc_eq_Ioc hΔpos.le hΔ_lt.le, Ioc_union_Ioi_eq_Ioi (hΔpos.trans hΔ_lt).le]
  refine ⟨integrableOn_univ.mp h_int_univ, ?_, ?_, ?_⟩
  · -- `∫ |fwExtPsi| = 1`
    rw [← setIntegral_univ, ← hunion_univ,
      setIntegral_union hu_1234 measurableSet_Ici ((hI_left_abs_int.union hI_mid_abs_int).union hI_midR_abs_int) hI_far_abs_int,
      setIntegral_union hu_123 measurableSet_Ioo (hI_left_abs_int.union hI_mid_abs_int) hI_midR_abs_int,
      setIntegral_union hu_12 measurableSet_Icc hI_left_abs_int hI_mid_abs_int,
      hI_left_abs_eq, hI_mid_abs_eq, hI_midR_abs_eq, hI_far_abs_eq, add_zero,
      show (∫ t in Ioi Δn, |f_raw t|) + (∫ t in Ioc Δp Δn, |f_raw t|) + (∫ t in Ioc 0 Δp, |f_raw t|) =
        ((∫ t in Ioc 0 Δp, |f_raw t|) + (∫ t in Ioc Δp Δn, |f_raw t|)) + ∫ t in Ioi Δn, |f_raw t| by ring]
    rw [← setIntegral_union ht_disj1 measurableSet_Ioc (hf_raw_abs_int.mono_set Ioc_subset_Ioi_self)
        (hf_raw_abs_int.mono_set (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi hΔpos.le))),
      ← setIntegral_union ht_disj2 measurableSet_Ioi
        ((hf_raw_abs_int.mono_set Ioc_subset_Ioi_self).union
          (hf_raw_abs_int.mono_set (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi hΔpos.le))))
        (hf_raw_abs_int.mono_set (Ioi_subset_Ioi (hΔpos.trans hΔ_lt).le)),
      ht_union]
    have heq : ∫ t in Ioi 0, |f_raw t| =
        (prob.cardyNorm (c' / 12) g)⁻¹ * ∫ t in Ioi 0, |g t| * prob.cardyV (c' / 12) t := by
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      dsimp [f_raw]
      rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr hM_pos.le), abs_mul,
        abs_of_nonneg (hV_nn t (mem_Ioi.mp ht).le)]
    have hnorm_eq : ∫ t in Ioi 0, |g t| * prob.cardyV (c' / 12) t = prob.cardyNorm (c' / 12) g := rfl
    rw [heq, hnorm_eq, inv_mul_cancel₀ hM_pos.ne']
  · -- `∫ fwExtPsi = M⁻¹ * ∫_{Ioi 0} g * V`
    rw [← setIntegral_univ, ← hunion_univ,
      setIntegral_union hu_1234 measurableSet_Ici ((hI_left_int.union hI_mid_int).union hI_midR_int) hI_far_int,
      setIntegral_union hu_123 measurableSet_Ioo (hI_left_int.union hI_mid_int) hI_midR_int,
      setIntegral_union hu_12 measurableSet_Icc hI_left_int hI_mid_int,
      hI_left_eq, hI_mid_eq, hI_midR_eq, hI_far_eq, add_zero,
      show (∫ t in Ioi Δn, f_raw t) + (∫ t in Ioc Δp Δn, f_raw t) + (∫ t in Ioc 0 Δp, f_raw t) =
        ((∫ t in Ioc 0 Δp, f_raw t) + (∫ t in Ioc Δp Δn, f_raw t)) + ∫ t in Ioi Δn, f_raw t by ring]
    rw [← setIntegral_union ht_disj1 measurableSet_Ioc (hf_raw_int.mono_set Ioc_subset_Ioi_self)
        (hf_raw_int.mono_set (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi hΔpos.le))),
      ← setIntegral_union ht_disj2 measurableSet_Ioi
        ((hf_raw_int.mono_set Ioc_subset_Ioi_self).union
          (hf_raw_int.mono_set (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi hΔpos.le))))
        (hf_raw_int.mono_set (Ioi_subset_Ioi (hΔpos.trans hΔ_lt).le)),
      ht_union, ← integral_const_mul]
  · -- `∫_{Ioi R} |fwExtPsi| = ∫_{R..A²} ‖psiTilde‖ + deltaLobe` for `0 ≤ R ≤ A²`
    intro R hR0 hRA
    have huR_disj1 : Disjoint (Ioc R (A ^ 2)) (Ioo (A ^ 2) (A ^ 2 + Δp)) :=
      Set.disjoint_left.mpr fun _ hx1 hx2 => absurd hx2.1 (not_lt.mpr hx1.2)
    have huR_disj2 : Disjoint (Ioc R (A ^ 2) ∪ Ioo (A ^ 2) (A ^ 2 + Δp)) (Ici (A ^ 2 + Δp)) :=
      Set.disjoint_left.mpr fun _ hx1 hx2 => by
        rcases hx1 with h1 | h2
        · linarith [h1.2, hΔpos, mem_Ici.mp hx2]
        · exact absurd h2.2 (not_lt.mpr hx2)
    have huR_union :
        (Ioc R (A ^ 2) ∪ Ioo (A ^ 2) (A ^ 2 + Δp)) ∪ Ici (A ^ 2 + Δp) = Ioi R := by
      ext u
      simp only [mem_union, mem_Ioc, mem_Ioo, mem_Ici, mem_Ioi]
      constructor
      · rintro ((h1 | h2) | h3)
        · exact h1.1
        · exact hRA.trans_lt h2.1
        · linarith
      · intro huR
        rcases le_or_gt u (A ^ 2) with h1 | h1
        · exact Or.inl (Or.inl ⟨huR, h1⟩)
        · rcases lt_or_ge u (A ^ 2 + Δp) with h2 | h2
          · exact Or.inl (Or.inr ⟨h1, h2⟩)
          · exact Or.inr h2
    have hI_R_abs_int : IntegrableOn (fun u => |fwExtPsi prob c' A g u|) (Ioc R (A ^ 2)) :=
      hI_mid_abs_int.mono_set (Ioc_subset_Icc_self.trans (Icc_subset_Icc (by linarith) le_rfl))
    rw [← huR_union,
      setIntegral_union huR_disj2 measurableSet_Ici (hI_R_abs_int.union hI_midR_abs_int) hI_far_abs_int,
      setIntegral_union huR_disj1 measurableSet_Ioo hI_R_abs_int hI_midR_abs_int,
      hI_far_abs_eq, add_zero]
    have h_left_eq : ∫ u in Ioc R (A ^ 2), |fwExtPsi prob c' A g u| =
        ∫ u in R..(A ^ 2), ‖psiTilde prob c' g (u : ℂ)‖ := by
      rw [intervalIntegral.integral_of_le hRA]
      refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
      have hu_abs : |u| ≤ A ^ 2 := abs_le.mpr ⟨by linarith [hu.1], hu.2⟩
      rw [fwExtPsi_eq_psiTilde hu_abs]
      have him := psiTilde_im_ofReal prob hc'_pos hg (hu_abs.trans hA2_vir)
      rw [Complex.norm_def, Complex.normSq_apply, him, mul_zero, add_zero, ← sq, Real.sqrt_sq_eq_abs]
    have h_right_eq : ∫ u in Ioo (A ^ 2) (A ^ 2 + Δp), |fwExtPsi prob c' A g u| =
        deltaLobe prob D.r_1 c' g := by
      rw [hI_midR_abs_eq]
      unfold deltaLobe
      rw [intervalIntegral.integral_of_le hΔpos.le, ← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
      dsimp [f_raw]
      rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr hM_pos.le), abs_mul,
        abs_of_nonneg (hV_nn t ht.1.le)]
    rw [h_left_eq, h_right_eq]

private lemma fwExtPsi_tail_nonneg {prob : FixedWeightProblem} (D : UniformPropositionPData prob)
    {c' T : ℝ} (hc' : D.c₀ ≤ c') {g : ℝ → ℝ} (hg : TestClass prob (c' / 12) g)
    (hM_pos : 0 < prob.cardyNorm (c' / 12) g) (htail : ∀ t ≥ T, 0 ≤ g t)
    (u : ℝ) (hu : u ≤ fwExtUT c' (chartAC D.r_1 c') T) :
    0 ≤ fwExtPsi prob c' (chartAC D.r_1 c') g u := by
  set A := chartAC D.r_1 c'
  set Δp := virasoroDeltaChart c' (A ^ 2)
  set Δn := virasoroDeltaChart c' (-(A ^ 2))
  have hc'_pos : 0 < c' := D.hc₀_pos.trans_le hc'
  have hA2_nn : 0 ≤ A ^ 2 := sq_nonneg _
  have hA2_vir : A ^ 2 ≤ virasoroAC c' ^ 2 := chartAC_sq_le_virasoroAC_sq D.hr1_pos hc'_pos.le
  have hΔpos : 0 < Δp :=
    virasoroDeltaChart_pos hc'_pos (chart_real_abs_le_virasoro D.hr1_pos hc'_pos (by rw [abs_of_nonneg hA2_nn]))
  have hanti := virasoroDeltaChart_strictAnti hc'_pos
  have hV_nn : ∀ t, 0 ≤ t → 0 ≤ prob.cardyV (c' / 12) t := fun t ht => D.cardyV_nonneg hc' ht
  rcases le_or_gt (A ^ 2 + Δp) u with hfar | hlt_far
  · rw [fwExtPsi_far_right hA2_nn hfar hΔpos]
  rcases lt_or_ge (A ^ 2) u with hmidR | hle_R
  · -- `A² < u < A² + Δp`
    rw [fwExtPsi_mid_right hA2_nn hmidR hlt_far]
    have hT_lt : T < Δp := by
      by_contra hge
      push Not at hge
      by_cases hle_n : T ≤ Δn
      · have hut_eq : fwExtUT c' A T = chartUT c' T := fwExtUT_mid hge hle_n
        have hmem := (chartUT_mem_Icc_of_between' D.hr1_pos hc'_pos hge hle_n).1
        linarith [hmem.2]
      · have hut_eq : fwExtUT c' A T = -(A ^ 2) - (T - Δn) := fwExtUT_gt hge (not_le.mp hle_n)
        linarith
    have hut_eq : fwExtUT c' A T = A ^ 2 + (Δp - T) := fwExtUT_lt hT_lt
    rw [hut_eq] at hu
    have ht_ge : T ≤ Δp - (u - A ^ 2) := by linarith
    have ht_pos : 0 < Δp - (u - A ^ 2) := by linarith
    exact mul_nonneg (inv_nonneg.mpr hM_pos.le)
      (mul_nonneg (htail _ ht_ge) (hV_nn _ ht_pos.le))
  rcases le_or_gt (-(A ^ 2)) u with hmid | hleft
  · -- `|u| ≤ A²`
    have hu_abs : |u| ≤ A ^ 2 := abs_le.mpr ⟨hmid, hle_R⟩
    rw [fwExtPsi_eq_psiTilde hu_abs, psiTilde_re_ofReal prob hc'_pos hg (hu_abs.trans hA2_vir)]
    have hder_le := virasoroDeltaChart_deriv_le hc'_pos (abs_le.mp (hu_abs.trans hA2_vir))
    have hc13_pos : 0 < c' ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hc'_pos _
    have hnd_pos : 0 < -(deriv (virasoroDeltaChart c') u) := by
      have := mul_pos (half_pos cStar_pos) hc13_pos; linarith
    have ht_pos : 0 < virasoroDeltaChart c' u := virasoroDeltaChart_pos hc'_pos (hu_abs.trans hA2_vir)
    have hT_le_Δu : T ≤ virasoroDeltaChart c' u := by
      by_cases hTp : T < Δp
      · have hΔu : Δp ≤ virasoroDeltaChart c' u :=
          hanti.antitoneOn ⟨by linarith [hA2_vir, hmid], hle_R.trans hA2_vir⟩
            ⟨by linarith [hA2_vir], hA2_vir⟩ hle_R
        exact hTp.le.trans hΔu
      · have hTp' : Δp ≤ T := not_lt.mp hTp
        have hTn : T ≤ Δn := by
          by_contra hgt
          have hut_eq : fwExtUT c' A T = -(A ^ 2) - (T - Δn) := fwExtUT_gt hTp' (not_le.mp hgt)
          linarith [hut_eq]
        obtain ⟨hmem, heq⟩ := chartUT_mem_Icc_of_between' D.hr1_pos hc'_pos hTp' hTn
        have hut_eq : fwExtUT c' A T = chartUT c' T := fwExtUT_mid hTp' hTn
        rw [hut_eq] at hu
        rw [← heq]
        exact hanti.antitoneOn ⟨by linarith [hA2_vir, hmid], hle_R.trans hA2_vir⟩
          ⟨by linarith [hA2_vir, hmem.1], hmem.2.trans hA2_vir⟩ hu
    exact mul_nonneg (mul_nonneg (inv_nonneg.mpr hM_pos.le) hnd_pos.le)
      (mul_nonneg (htail _ hT_le_Δu) (hV_nn _ ht_pos.le))
  · -- `u < -A²`
    rw [fwExtPsi_left hleft]
    have ht_ge : T ≤ Δn + (-(A ^ 2) - u) := by
      by_cases hTn : T ≤ Δn
      · linarith
      · have hTp' : Δp ≤ T := by
          have : Δp ≤ Δn :=
            hanti.antitoneOn (a := -(A ^ 2)) (b := A ^ 2)
              ⟨by linarith [hA2_vir], by linarith [hA2_vir]⟩ ⟨by linarith [hA2_vir], hA2_vir⟩
              (by linarith)
          linarith [not_le.mp hTn]
        have hut_eq : fwExtUT c' A T = -(A ^ 2) - (T - Δn) := fwExtUT_gt hTp' (not_le.mp hTn)
        linarith
    have ht_pos : 0 < Δn + (-(A ^ 2) - u) :=
      lt_of_lt_of_le (virasoroDeltaChart_pos hc'_pos (by rw [abs_neg, abs_of_nonneg hA2_nn]; exact hA2_vir))
        (by linarith)
    exact mul_nonneg (inv_nonneg.mpr hM_pos.le) (mul_nonneg (htail _ ht_ge) (hV_nn _ ht_pos.le))

private lemma fwExtUT_bddBelow_implies_T_le {r1 c' T B K : ℝ} (hr1 : 0 < r1) (hc' : 0 < c')
    (hK : 0 ≤ K) (hKB : -K ≤ B) (hKA : K < chartAC r1 c' ^ 2)
    (hB : B ≤ fwExtUT c' (chartAC r1 c') T) :
    T ≤ virasoroDeltaChart c' (-K) := by
  set A := chartAC r1 c'
  set Δp := virasoroDeltaChart c' (A ^ 2)
  set Δn := virasoroDeltaChart c' (-(A ^ 2))
  have hA2_vir : A ^ 2 ≤ virasoroAC c' ^ 2 := chartAC_sq_le_virasoroAC_sq hr1 hc'.le
  have hanti := virasoroDeltaChart_strictAnti hc'
  by_cases hTp : T < Δp
  · have hle : Δp ≤ virasoroDeltaChart c' (-K) :=
      hanti.antitoneOn ⟨by linarith [hKA, hA2_vir], by linarith [hK, hA2_vir]⟩
        ⟨by linarith [hA2_vir, hK, hKA], hA2_vir⟩ (by linarith [hK, hKA])
    exact hTp.le.trans hle
  · have hTp' : Δp ≤ T := not_lt.mp hTp
    have hTn : T ≤ Δn := by
      by_contra hgt
      have hut_eq : fwExtUT c' A T = -(A ^ 2) - (T - Δn) := fwExtUT_gt hTp' (not_le.mp hgt)
      linarith
    obtain ⟨hmem, heq⟩ := chartUT_mem_Icc_of_between' hr1 hc' hTp' hTn
    have hut_eq : fwExtUT c' A T = chartUT c' T := fwExtUT_mid hTp' hTn
    rw [hut_eq] at hB
    rw [← heq]
    exact hanti.antitoneOn ⟨by linarith [hKA, hA2_vir], by linarith [hK, hA2_vir]⟩
      ⟨by linarith [hmem.1, hA2_vir], hmem.2.trans hA2_vir⟩ (hKB.trans hB)

/-! ### Main Paper II `FT-CC` Instantiations -/

theorem fwExtPsi_core_props (prob : FixedWeightProblem)
    {c' T : ℕ → ℝ} {g : ℕ → ℝ → ℝ}
    (hc' : Tendsto c' atTop atTop)
    (hg : ∀ᶠ n in atTop, prob.IsWeaklyFeasible (c' n / 12) (T n) (g n)) :
    let D := fwD prob
    let ψ : ℕ → ℝ → ℝ := fun n => fwExtPsi prob (c' n) (chartAC D.r_1 (c' n)) (g n)
    let uT : ℕ → ℝ := fun n => fwExtUT (c' n) (chartAC D.r_1 (c' n)) (T n)
    (∀ᶠ n in atTop, Integrable (ψ n)) ∧
    (∀ᶠ n in atTop, ∫ u : ℝ, |ψ n u| = 1) ∧
    (∀ᶠ n in atTop, ∫ u : ℝ, ψ n u ≤ 0) ∧
    (∀ᶠ n in atTop, ∀ u : ℝ, u ≤ uT n → 0 ≤ ψ n u) := by
  intro D ψ uT
  obtain ⟨c₂, _, _, _, hpart2⟩ := lemmaQ_general_part2 D
  have hev_base : ∀ᶠ n in atTop,
      c₂ ≤ c' n ∧ D.c₀ ≤ c' n ∧ 12 * prob.totalShift ≤ c' n ∧
      prob.IsWeaklyFeasible (c' n / 12) (T n) (g n) :=
    (hc'.eventually (eventually_ge_atTop c₂)).and <|
      (hc'.eventually (eventually_ge_atTop D.c₀)).and <|
      (hc'.eventually (eventually_ge_atTop (12 * prob.totalShift))).and hg
  have hev_all : ∀ᶠ n in atTop,
      Integrable (ψ n) ∧ (∫ u : ℝ, |ψ n u| = 1) ∧ (∫ u : ℝ, ψ n u ≤ 0) ∧
      (∀ u : ℝ, u ≤ uT n → 0 ≤ ψ n u) := by
    filter_upwards [hev_base] with n ⟨hc₂n, hc₀n, hshn, hwf⟩
    have hM_pos : 0 < prob.cardyNorm (c' n / 12) (g n) :=
      cardyNorm_pos_of_nonzero_general prob (by linarith : prob.totalShift ≤ c' n / 12) hwf.1 hwf.2.1
    obtain ⟨han, _, _⟩ := hpart2 hc₂n hwf.1 hM_pos
    obtain ⟨h1, h2, h3, _⟩ := fwExtPsi_integrals D hc₀n hwf.1 hM_pos han
    have hle0 : ∫ u : ℝ, ψ n u ≤ 0 := by
      rw [h3]
      have hgv_le : ∫ t in Ioi (0 : ℝ), g n t * prob.cardyV (c' n / 12) t ≤ 0 := by
        have hgvac : 0 ≤ prob.gVac (c' n / 12) (g n) := hwf.2.2.1
        unfold FixedWeightProblem.gVac at hgvac
        nlinarith [Real.pi_pos]
      exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hM_pos.le) hgv_le
    exact ⟨h1, h2, hle0, fun u hu => fwExtPsi_tail_nonneg D hc₀n hwf.1 hM_pos hwf.2.2.2 u hu⟩
  exact ⟨hev_all.mono fun _ h => h.1, hev_all.mono fun _ h => h.2.1,
    hev_all.mono fun _ h => h.2.2.1, hev_all.mono fun _ h => h.2.2.2⟩

/-- **Fixed-weight Chart Compactness (`FT-CC`, Paper II instances)**: for any fixed-weight
problem `prob`, any Hermite–Biehler datum `H`, and any sequence of weakly feasible tests `g n`
at `c' n → ∞` with `0 ≤ g n (Δ_{c' n}(uSite t n))` at the prescribed nodes `uSite t n → t`
(`t ∈ H.S \ {H.tm}`), the extended transported densities `fwExtPsi` and thresholds `fwExtUT`
form a `ChartCompactness ℕ atTop H` package. -/
noncomputable def fixedWeight_chartCompactness (prob : FixedWeightProblem)
    (H : HermiteBiehlerData) {c' T : ℕ → ℝ} {g : ℕ → ℝ → ℝ} {uSite : H.S → ℕ → ℝ}
    (hc' : Tendsto c' atTop atTop)
    (hg : ∀ᶠ n in atTop, prob.IsWeaklyFeasible (c' n / 12) (T n) (g n))
    (huSite : ∀ t : H.S, (t : ℝ) ≠ H.tm → Tendsto (uSite t) atTop (𝓝 (t : ℝ)))
    (hnode : ∀ t : H.S, (t : ℝ) ≠ H.tm →
      ∀ᶠ n in atTop, 0 ≤ g n (virasoroDeltaChart (c' n) (uSite t n))) :
    ChartCompactness ℕ atTop H where
  ψ := fun n => fwExtPsi prob (c' n) (chartAC (fwD prob).r_1 (c' n)) (g n)
  uT := fun n => fwExtUT (c' n) (chartAC (fwD prob).r_1 (c' n)) (T n)
  uSite := uSite
  ψ_int := (fwExtPsi_core_props prob hc' hg).1
  ψ_l1_eq_one := (fwExtPsi_core_props prob hc' hg).2.1
  ψ_integral_le_zero := (fwExtPsi_core_props prob hc' hg).2.2.1
  ψ_tail_nonneg := (fwExtPsi_core_props prob hc' hg).2.2.2
  ψ_site_nonneg := by
    intro t ht
    let D := fwD prob
    obtain ⟨c₂, _, _, _, hpart2⟩ := lemmaQ_general_part2 D
    have hA2_tend : Tendsto (fun n => chartAC D.r_1 (c' n) ^ 2) atTop atTop :=
      (tendsto_chartAC_sq D.hr1_pos).comp hc'
    have hbd : ∀ᶠ n in atTop, |uSite t n| ≤ chartAC D.r_1 (c' n) ^ 2 := by
      have hb1 : ∀ᶠ n in atTop, |uSite t n| ≤ |(t : ℝ)| + 1 :=
        (huSite t ht).abs.eventually (eventually_le_nhds (by linarith))
      filter_upwards [hb1, hA2_tend.eventually (eventually_ge_atTop (|(t : ℝ)| + 1))] with n h1 h2
      exact h1.trans h2
    filter_upwards [hc'.eventually (eventually_ge_atTop c₂),
      hc'.eventually (eventually_ge_atTop (12 * prob.totalShift)), hg, hbd, hnode t ht] with
      n hc₂n hshn hwf hbu hgn
    have hM_pos : 0 < prob.cardyNorm (c' n / 12) (g n) :=
      cardyNorm_pos_of_nonzero_general prob (by linarith : prob.totalShift ≤ c' n / 12) hwf.1 hwf.2.1
    rw [fwExtPsi_eq_psiTilde hbu]
    exact ((hpart2 hc₂n hwf.1 hM_pos).2.1 (uSite t n) hbu).2.mp hgn
  uSite_tendsto := huSite
  tail_tight := by
    intro ε hε
    let D := fwD prob
    obtain ⟨c₂, C₀, _, hC₀, hpart2⟩ := lemmaQ_general_part2 D
    obtain ⟨c_gap, C_gap, κ_gap, _, _, hκ_gap, hgap, _⟩ := deltaLobe_gap_general D
    have hR₀_ex : ∃ R₀ : ℝ, 1 ≤ R₀ ∧ (6 / 5 : ℝ) * C₀ * Real.exp (-(5 / 6 : ℝ) * R₀) ≤ ε / 2 := by
      have hlim : Tendsto (fun R : ℝ => (6 / 5 : ℝ) * C₀ * Real.exp (-(5 / 6 : ℝ) * R))
          atTop (𝓝 0) := by
        have h1 : Tendsto (fun R : ℝ => -(5 / 6 : ℝ) * R) atTop atBot :=
          Tendsto.const_mul_atTop_of_neg (by norm_num : -(5 / 6 : ℝ) < 0) tendsto_id
        simpa using ((Real.tendsto_exp_atBot.comp h1).const_mul ((6 / 5 : ℝ) * C₀))
      obtain ⟨R₀, hR₀⟩ := eventually_atTop.1
        ((eventually_ge_atTop (1 : ℝ)).and (hlim.eventually (eventually_le_nhds (half_pos hε))))
      exact ⟨R₀, (hR₀ R₀ le_rfl).1, (hR₀ R₀ le_rfl).2⟩
    obtain ⟨R₀, hR₀1, hR₀_eps⟩ := hR₀_ex
    refine ⟨R₀, fun R hRR₀ => ?_⟩
    have hR1 : 1 ≤ R := hR₀1.trans hRR₀
    have hA2_tend : Tendsto (fun n => chartAC D.r_1 (c' n) ^ 2) atTop atTop :=
      (tendsto_chartAC_sq D.hr1_pos).comp hc'
    have hsig_tend : Tendsto (fun n => generalSigma D.p_e (c' n)) atTop (𝓝 0) :=
      (generalSigma_tendsto_zero D.p_e).comp hc'
    have hdl_tend : Tendsto (fun n => C_gap * Real.exp (-κ_gap * c' n)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n => -κ_gap * c' n) atTop atBot :=
        hc'.const_mul_atTop_of_neg (by linarith)
      simpa using (Real.tendsto_exp_atBot.comp h1).const_mul C_gap
    filter_upwards [hc'.eventually (eventually_ge_atTop c₂),
      hc'.eventually (eventually_ge_atTop c_gap),
      hc'.eventually (eventually_ge_atTop D.c₀),
      hc'.eventually (eventually_ge_atTop (12 * prob.totalShift)), hg,
      hA2_tend.eventually (eventually_ge_atTop R),
      hc'.eventually (eventually_ge_atTop (1 : ℝ)),
      hsig_tend.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
      hdl_tend.eventually (eventually_le_nhds (half_pos hε))] with
      n hc₂n hcgapn hc₀n hshn hwf hRA hc1 hsig_half hdl_eps
    have hc'_pos : 0 < c' n := D.hc₀_pos.trans_le hc₀n
    have hM_pos : 0 < prob.cardyNorm (c' n / 12) (g n) :=
      cardyNorm_pos_of_nonzero_general prob (by linarith : prob.totalShift ≤ c' n / 12) hwf.1 hwf.2.1
    obtain ⟨han, _, henv⟩ := hpart2 hc₂n hwf.1 hM_pos
    obtain ⟨_, _, _, h4⟩ := fwExtPsi_integrals D hc₀n hwf.1 hM_pos han
    rw [h4 R (by linarith) hRA]
    have hcont : ContinuousOn (fun x : ℝ => psiTilde prob (c' n) (g n) (x : ℂ))
        (Icc R (chartAC D.r_1 (c' n) ^ 2)) :=
      (han.continuousOn.mono (closedBall_chartAC_subset_psiDom D.hr1_pos hc'_pos)).comp
        continuous_ofReal.continuousOn fun x hx => by
          rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_le]
          exact ⟨by linarith [hx.1], hx.2⟩
    have hΨ_env : ∀ x : ℝ, 0 < x → x ≤ chartAC D.r_1 (c' n) ^ 2 →
        ‖psiTilde prob (c' n) (g n) (x : ℂ)‖ ≤
          C₀ * airyEnv (x : ℂ) * Real.exp (generalSigma D.p_e (c' n) * √x) * x⁻¹ := by
      intro x hx0 hxA
      have hmem : (x : ℂ) ∈ closedBall (0 : ℂ) (chartAC D.r_1 (c' n) ^ 2) := by
        rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
        exact hxA
      have hnot : ¬ ((x : ℂ).im = 0 ∧ (x : ℂ).re ≤ 0) := fun ⟨_, hle⟩ => by simp at hle; linarith
      have hb := henv (x : ℂ) hmem hnot
      have hcpow : ((x : ℂ) ^ (1 / 2 : ℂ)).re = √x := by
        rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
          ← Complex.ofReal_cpow hx0.le, Complex.ofReal_re, Real.sqrt_eq_rpow]
      have hnorm : ‖(x : ℂ)‖ ^ (-(1 / 2 : ℝ)) * (√x)⁻¹ = x⁻¹ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0, Real.sqrt_eq_rpow,
          ← Real.rpow_neg hx0.le, ← Real.rpow_add hx0]
        norm_num
        exact Real.rpow_neg_one x
      rw [hcpow] at hb
      calc ‖psiTilde prob (c' n) (g n) (x : ℂ)‖
          ≤ C₀ * airyEnv (x : ℂ) * Real.exp (generalSigma D.p_e (c' n) * √x) *
              (‖(x : ℂ)‖ ^ (-(1 / 2 : ℝ)) * (√x)⁻¹) := by simpa only [mul_assoc] using hb
        _ = C₀ * airyEnv (x : ℂ) * Real.exp (generalSigma D.p_e (c' n) * √x) * x⁻¹ := by
              rw [hnorm]
    have htail_le := clarkTail_norm_le hC₀ (generalSigma_nonneg D.hp_e_nn hc1) hsig_half
      hR1 hRA hcont hΨ_env
    have htail_le' : (6 / 5 : ℝ) * C₀ * Real.exp (-(5 / 6 : ℝ) * R) ≤ ε / 2 := by
      refine le_trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)) hR₀_eps
      linarith
    have hdl_le : deltaLobe prob D.r_1 (c' n) (g n) ≤ ε / 2 :=
      (hgap hcgapn hwf.1 hM_pos).trans hdl_eps
    linarith
  compactness_subseq := by
    intro ns hns ⟨B, hB⟩
    let D := fwD prob
    obtain ⟨c₂, _, hc₂, _, _⟩ := lemmaQ_general_part2 D
    obtain ⟨c_gap, _, _, hc_gap, _, _, _, hgap_wf⟩ := deltaLobe_gap_general D
    let K : ℝ := max 0 (-B) + 1
    have hK0 : 0 ≤ K := by positivity
    have hKB : -K ≤ B := by
      have h1 : -B ≤ max 0 (-B) := le_max_right _ _
      linarith
    have hc's : Tendsto (fun k => c' (ns k)) atTop atTop := hc'.comp hns
    have hAs : Tendsto (fun k => chartAC D.r_1 (c' (ns k)) ^ 2) atTop atTop :=
      (tendsto_chartAC_sq D.hr1_pos).comp hc's
    have hev_ns : ∀ᶠ k in atTop,
        c₂ ≤ c' (ns k) ∧ c_gap ≤ c' (ns k) ∧ D.c₀ ≤ c' (ns k) ∧
        12 * prob.totalShift ≤ c' (ns k) ∧
        prob.IsWeaklyFeasible (c' (ns k) / 12) (T (ns k)) (g (ns k)) :=
      ((hc's.eventually (eventually_ge_atTop c₂)).and
        ((hc's.eventually (eventually_ge_atTop c_gap)).and
          ((hc's.eventually (eventually_ge_atTop D.c₀)).and
            (hc's.eventually (eventually_ge_atTop (12 * prob.totalShift)))))).and
        (hg.filter_mono hns) |>.mono
        fun _ ⟨⟨h1, h2, h3, h4⟩, h5⟩ => ⟨h1, h2, h3, h4, h5⟩
    have hsf_s : ∀ᶠ k in atTop,
        IsSlackFeasible prob (c' (ns k) / 12) (T (ns k)) 0 (g (ns k)) := by
      filter_upwards [hev_ns] with k ⟨_, _, _, hshk, hwf⟩
      have hM : 0 < prob.cardyNorm (c' (ns k) / 12) (g (ns k)) :=
        cardyNorm_pos_of_nonzero_general prob (by linarith : prob.totalShift ≤ c' (ns k) / 12) hwf.1 hwf.2.1
      have hgv : ∫ t in Ioi (0 : ℝ), g (ns k) t * prob.cardyV (c' (ns k) / 12) t ≤ 0 := by
        have hgvac : 0 ≤ prob.gVac (c' (ns k) / 12) (g (ns k)) := hwf.2.2.1
        unfold FixedWeightProblem.gVac at hgvac
        nlinarith [Real.pi_pos]
      exact ⟨hwf.1, hM, by simpa using hgv, hwf.2.2.2⟩
    have hK_ev : ∀ᶠ k in atTop, T (ns k) ≤ virasoroDeltaChart (c' (ns k)) (-K) := by
      filter_upwards [hc's.eventually (eventually_gt_atTop (0 : ℝ)),
        hAs.eventually (eventually_gt_atTop K)] with k hck hKA
      exact fwExtUT_bddBelow_implies_T_le D.hr1_pos hck hK0 hKB hKA (hB k)
    obtain ⟨C₀', N, S, _, _, _⟩ := exists_densitySeq D (Q := fun _ => True)
      (Filter.Eventually.of_forall fun _ => trivial) hc's
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
      (Eventually.of_forall fun _ => le_rfl) hsf_s ⟨K, hK0, hK_ev⟩
    obtain ⟨φ, Φ, hφ_mono, hU, hΦ_diff, hΦ_bd⟩ := density_exists_subseq S
    have huT_S_bdd : ∃ R_hi : ℝ, ∀ᶠ j in atTop,
        chartUT (c' (ns (max j N))) (T (ns (max j N))) ≤ R_hi := by
      have hlim_tb := tailBound_tendsto C₀'
      obtain ⟨R_hi, hR1, hR_tb⟩ : ∃ R_hi : ℕ, 1 ≤ R_hi ∧ tailBound C₀' R_hi < 1 / 4 := by
        obtain ⟨M, hM⟩ := eventually_atTop.1
          ((eventually_ge_atTop (1 : ℕ)).and
            (hlim_tb.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 4))))
        exact ⟨M, (hM M le_rfl).1, (hM M le_rfl).2⟩
      refine ⟨(R_hi : ℝ), ?_⟩
      have hR_le : ∀ᶠ j in atTop, (R_hi : ℝ) ≤ chartAC D.r_1 (c' (ns (max j N))) ^ 2 :=
        S.hR (eventually_ge_atTop (R_hi : ℝ))
      have hδ_lt : ∀ᶠ j in atTop,
          deltaLobe prob D.r_1 (c' (ns (max j N))) (g (ns (max j N))) + 0 < 1 / 4 :=
        S.hδ (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 4))
      have hς0 : ∀ᶠ j in atTop, 0 ≤ generalSigma D.p_e (c' (ns (max j N))) := S.hς0
      have hς2 : ∀ᶠ j in atTop, generalSigma D.p_e (c' (ns (max j N))) ≤ 1 / 2 :=
        S.hς (Iic_mem_nhds (by norm_num))
      filter_upwards [hR_le, hδ_lt, hς0, hς2] with j hjR hjδ hjς0 hjς2
      by_contra hgt
      push Not at hgt
      have hneg_ge := (S.hspec j).symm_neg_ge S.hC0 hjς0 hjς2 (by exact_mod_cast hR1) hjR
        (by linarith [hgt.le])
      have hzero : ∫ x in (-(R_hi : ℝ))..(R_hi : ℝ),
          max 0 (-(psiTilde prob (c' (ns (max j N))) (g (ns (max j N))) (x : ℂ)).re) = 0 := by
        have hle : -(R_hi : ℝ) ≤ R_hi := by linarith [(Nat.cast_nonneg R_hi : (0 : ℝ) ≤ R_hi)]
        rw [intervalIntegral.integral_of_le hle]
        refine setIntegral_eq_zero_of_forall_eq_zero fun x hx => ?_
        have hx_nn := (S.hspec j).nonneg x
          ⟨by linarith [hx.1, hjR], hx.2.trans hjR⟩ (by linarith [hx.2, hgt])
        exact max_eq_left (by linarith)
      rw [hzero] at hneg_ge
      linarith
    have hT_between : ∀ᶠ k in atTop,
        virasoroDeltaChart (c' (ns k)) (chartAC D.r_1 (c' (ns k)) ^ 2) < T (ns k) ∧
        T (ns k) ≤ virasoroDeltaChart (c' (ns k)) (-(chartAC D.r_1 (c' (ns k)) ^ 2)) := by
      filter_upwards [hev_ns, hAs.eventually (eventually_gt_atTop K),
        hc's.eventually (eventually_gt_atTop (0 : ℝ)), hK_ev] with k ⟨_, hcgapk, _, _, hwf⟩ hKA hck hTk
      exact ⟨(hgap_wf hcgapk hwf).2.2.2, (interior_of_le_neg D.hr1_pos hck hK0 hKA hTk).le⟩
    let base : ℕ → ℕ := fun k => φ (k + N)
    have hbase_mono : StrictMono base := fun a b hab => hφ_mono (by omega)
    have hbase_geN : ∀ k, N ≤ base k := fun k => le_trans (Nat.le_add_left N k) (hφ_mono.id_le (k + N))
    have hmax_eq : ∀ k, max (base k) N = base k := fun k => max_eq_left (hbase_geN k)
    obtain ⟨R_hi, hR_hi⟩ := huT_S_bdd
    obtain ⟨M_hi, hM_hi⟩ := eventually_atTop.1 (hR_hi.and hT_between)
    have huT_compact : ∀ k, fwExtUT (c' (ns (base (k + M_hi))))
        (chartAC D.r_1 (c' (ns (base (k + M_hi))))) (T (ns (base (k + M_hi)))) ∈
        Icc (min B R_hi) (max B R_hi) := by
      intro k
      have hk1 : B ≤ fwExtUT (c' (ns (base (k + M_hi))))
          (chartAC D.r_1 (c' (ns (base (k + M_hi))))) (T (ns (base (k + M_hi)))) := hB _
      have hidx_geM : M_hi ≤ base (k + M_hi) :=
        le_trans (Nat.le_add_left M_hi k) (hbase_mono.id_le (k + M_hi))
      have hpair := hM_hi _ hidx_geM
      have hle_R : chartUT (c' (ns (base (k + M_hi)))) (T (ns (base (k + M_hi)))) ≤ R_hi := by
        simpa only [hmax_eq] using hpair.1
      have huT_eq : fwExtUT (c' (ns (base (k + M_hi))))
          (chartAC D.r_1 (c' (ns (base (k + M_hi))))) (T (ns (base (k + M_hi)))) =
          chartUT (c' (ns (base (k + M_hi)))) (T (ns (base (k + M_hi)))) :=
        fwExtUT_mid hpair.2.1.le hpair.2.2
      exact ⟨(min_le_left _ _).trans hk1, (huT_eq ▸ hle_R).trans (le_max_right _ _)⟩
    obtain ⟨uLim, _, σ, hσ_mono, huLim⟩ :=
      isCompact_Icc.tendsto_subseq huT_compact
    let ms : ℕ → ℕ := fun k => base (σ k + M_hi)
    have hms_mono : StrictMono ms := fun a b hab =>
      hbase_mono (Nat.add_lt_add_right (hσ_mono hab) M_hi)
    have hC₀_pos : 0 ≤ limitGrowthConst C₀' := by
      unfold limitGrowthConst
      have := S.hC0
      positivity
    refine ⟨ms, uLim, Φ, limitGrowthConst C₀', (1 / 2 : ℝ), hms_mono, huLim, ?_, hΦ_diff,
      limit_integrable S hφ_mono hU hΦ_diff, hC₀_pos, fun z => hΦ_bd z, limit_real S hφ_mono hU⟩
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ]
    intro K _ hK
    obtain ⟨R, hKR⟩ := hK.isBounded.subset_closedBall (0 : ℝ)
    let Rpos : ℝ := max R 0
    have hKR' : K ⊆ closedBall (0 : ℝ) Rpos :=
      hKR.trans (closedBall_subset_closedBall (le_max_left R 0))
    let m : ℕ := ⌈Rpos⌉₊
    have hm_ge : Rpos ≤ (m : ℝ) + 1 := by
      have := Nat.le_ceil Rpos
      linarith
    rw [Metric.tendstoUniformlyOn_iff]
    intro δ hδ
    have hU_m := Metric.tendstoUniformlyOn_iff.mp (hU m) δ hδ
    let sub_φ : ℕ → ℕ := fun k => σ k + M_hi + N
    have hsub_φ_mono : StrictMono sub_φ := fun a b hab => by
      dsimp [sub_φ]; exact Nat.add_lt_add_right (Nat.add_lt_add_right (hσ_mono hab) M_hi) N
    have hU_sub : ∀ᶠ k in atTop, ∀ z ∈ closedBall (0 : ℂ) ((m : ℝ) + 1),
        dist (Φ z) (psiTilde prob (c' (ns (ms k))) (g (ns (ms k))) z) < δ := by
      filter_upwards [hU_m.filter_mono hsub_φ_mono.tendsto_atTop] with k hk z hz
      have hms_eq : φ (sub_φ k) = ms k := rfl
      have hmax_k : max (ms k) N = ms k := hmax_eq (σ k + M_hi)
      simpa only [hms_eq, hmax_k] using hk z hz
    have hA_ge : ∀ᶠ k in atTop, Rpos ≤ chartAC D.r_1 (c' (ns (ms k))) ^ 2 :=
      (hAs.comp hms_mono.tendsto_atTop).eventually (eventually_ge_atTop Rpos)
    filter_upwards [hU_sub, hA_ge] with k hk hAk u hu
    have hu_abs : |u| ≤ Rpos := by
      have := mem_closedBall_zero_iff.mp (hKR' hu)
      simpa [Real.norm_eq_abs] using this
    have hu_C : (u : ℂ) ∈ closedBall (0 : ℂ) ((m : ℝ) + 1) := by
      rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]
      exact hu_abs.trans hm_ge
    have hu_psi : fwExtPsi prob (c' (ns (ms k))) (chartAC D.r_1 (c' (ns (ms k)))) (g (ns (ms k))) u =
        (psiTilde prob (c' (ns (ms k))) (g (ns (ms k))) (u : ℂ)).re :=
      fwExtPsi_eq_psiTilde (hu_abs.trans hAk)
    rw [hu_psi, Real.dist_eq]
    have hd := Complex.abs_re_le_norm (Φ (u : ℂ) - psiTilde prob (c' (ns (ms k))) (g (ns (ms k))) (u : ℂ))
    rw [Complex.sub_re] at hd
    exact hd.trans_lt (by simpa [Complex.dist_eq] using hk (u : ℂ) hu_C)

/-- **Upper threshold convergence (`EReal` form, `ft:FT` / `bl:norm`(a)) via `ChartCompactness`**:
`limsup fwExtUT ≤ H.tm` in `EReal`, requiring no lower bound hypothesis on `fwExtUT`. -/
theorem fixedWeight_chartCompactness_limsup_ereal (prob : FixedWeightProblem)
    (H : HermiteBiehlerData) {c' T : ℕ → ℝ} {g : ℕ → ℝ → ℝ} {uSite : H.S → ℕ → ℝ}
    (hc' : Tendsto c' atTop atTop)
    (hg : ∀ᶠ n in atTop, prob.IsWeaklyFeasible (c' n / 12) (T n) (g n))
    (huSite : ∀ t : H.S, (t : ℝ) ≠ H.tm → Tendsto (uSite t) atTop (𝓝 (t : ℝ)))
    (hnode : ∀ t : H.S, (t : ℝ) ≠ H.tm →
      ∀ᶠ n in atTop, 0 ≤ g n (virasoroDeltaChart (c' n) (uSite t n))) :
    Filter.limsup
        (fun n => (fwExtUT (c' n) (chartAC (fwD prob).r_1 (c' n)) (T n) : EReal)) atTop ≤
      (H.tm : EReal) :=
  chartCompactness_limsup_ereal (fixedWeight_chartCompactness prob H hc' hg huSite hnode)

/-- **Upper threshold convergence (`ft:FT` / `bl:norm`(a)) via `ChartCompactness`** for any
fixed-weight problem `prob` and any Hermite–Biehler datum `H`, when `fwExtUT` is cobounded below. -/
theorem fixedWeight_chartCompactness_limsup (prob : FixedWeightProblem)
    (H : HermiteBiehlerData) {c' T : ℕ → ℝ} {g : ℕ → ℝ → ℝ} {uSite : H.S → ℕ → ℝ}
    (hc' : Tendsto c' atTop atTop)
    (hg : ∀ᶠ n in atTop, prob.IsWeaklyFeasible (c' n / 12) (T n) (g n))
    (huSite : ∀ t : H.S, (t : ℝ) ≠ H.tm → Tendsto (uSite t) atTop (𝓝 (t : ℝ)))
    (hnode : ∀ t : H.S, (t : ℝ) ≠ H.tm →
      ∀ᶠ n in atTop, 0 ≤ g n (virasoroDeltaChart (c' n) (uSite t n)))
    (hbdd : atTop.IsCoboundedUnder (· ≤ ·)
      (fun n => fwExtUT (c' n) (chartAC (fwD prob).r_1 (c' n)) (T n))) :
    Filter.limsup (fun n => fwExtUT (c' n) (chartAC (fwD prob).r_1 (c' n)) (T n)) atTop ≤
      H.tm :=
  chartCompactness_limsup (fixedWeight_chartCompactness prob H hc' hg huSite hnode) hbdd

/-- **Profile rigidity (`ft:FT` / `bl:norm`(b)) via `ChartCompactness`**: when `fwExtUT → H.tm`,
the extended transported density `fwExtPsi` converges locally uniformly on `ℝ` and in `L¹(ℝ)`
to `H.normG`. -/
theorem fixedWeight_chartCompactness_profile (prob : FixedWeightProblem)
    (H : HermiteBiehlerData) {c' T : ℕ → ℝ} {g : ℕ → ℝ → ℝ} {uSite : H.S → ℕ → ℝ}
    (hc' : Tendsto c' atTop atTop)
    (hg : ∀ᶠ n in atTop, prob.IsWeaklyFeasible (c' n / 12) (T n) (g n))
    (huSite : ∀ t : H.S, (t : ℝ) ≠ H.tm → Tendsto (uSite t) atTop (𝓝 (t : ℝ)))
    (hnode : ∀ t : H.S, (t : ℝ) ≠ H.tm →
      ∀ᶠ n in atTop, 0 ≤ g n (virasoroDeltaChart (c' n) (uSite t n)))
    (huT_lim : Tendsto (fun n => fwExtUT (c' n) (chartAC (fwD prob).r_1 (c' n)) (T n))
      atTop (𝓝 H.tm)) :
    TendstoLocallyUniformlyOn
      (fun n u => fwExtPsi prob (c' n) (chartAC (fwD prob).r_1 (c' n)) (g n) u)
      H.normG atTop univ ∧
    Tendsto
      (fun n => ∫ u : ℝ,
        |fwExtPsi prob (c' n) (chartAC (fwD prob).r_1 (c' n)) (g n) u - H.normG u|)
      atTop (𝓝 0) :=
  chartCompactness_profile (fixedWeight_chartCompactness prob H hc' hg huSite hnode) huT_lim

/-- **`FT-CC` Virasoro Airy-level instance (`virasoroProblem`, `HermiteBiehlerData.airy`)**. -/
noncomputable def fixedWeight_chartCompactness_virasoro
    {c' T : ℕ → ℝ} {g : ℕ → ℝ → ℝ}
    {uSite : HermiteBiehlerData.airy.S → ℕ → ℝ}
    (hc' : Tendsto c' atTop atTop)
    (hg : ∀ᶠ n in atTop, virasoroProblem.IsWeaklyFeasible (c' n / 12) (T n) (g n))
    (huSite : ∀ t : HermiteBiehlerData.airy.S, (t : ℝ) ≠ HermiteBiehlerData.airy.tm →
      Tendsto (uSite t) atTop (𝓝 (t : ℝ)))
    (hnode : ∀ t : HermiteBiehlerData.airy.S, (t : ℝ) ≠ HermiteBiehlerData.airy.tm →
      ∀ᶠ n in atTop, 0 ≤ g n (virasoroDeltaChart (c' n) (uSite t n))) :
    ChartCompactness ℕ atTop HermiteBiehlerData.airy :=
  fixedWeight_chartCompactness virasoroProblem HermiteBiehlerData.airy hc' hg huSite hnode

/-- **`FT-CC` fixed-weight Clark-level instance (`HermiteBiehlerData.clark hα`)**. -/
noncomputable def fixedWeight_chartCompactness_clark (prob : FixedWeightProblem)
    {α : ℝ} (hα : Real.sin α ≠ 0) {c' T : ℕ → ℝ} {g : ℕ → ℝ → ℝ}
    {uSite : (HermiteBiehlerData.clark hα).S → ℕ → ℝ}
    (hc' : Tendsto c' atTop atTop)
    (hg : ∀ᶠ n in atTop, prob.IsWeaklyFeasible (c' n / 12) (T n) (g n))
    (huSite : ∀ t : (HermiteBiehlerData.clark hα).S, (t : ℝ) ≠ (HermiteBiehlerData.clark hα).tm →
      Tendsto (uSite t) atTop (𝓝 (t : ℝ)))
    (hnode : ∀ t : (HermiteBiehlerData.clark hα).S, (t : ℝ) ≠ (HermiteBiehlerData.clark hα).tm →
      ∀ᶠ n in atTop, 0 ≤ g n (virasoroDeltaChart (c' n) (uSite t n))) :
    ChartCompactness ℕ atTop (HermiteBiehlerData.clark hα) :=
  fixedWeight_chartCompactness prob (HermiteBiehlerData.clark hα) hc' hg huSite hnode

/-- info: 'FormalResearch.ModularBootstrap.FoldTip.fixedWeight_chartCompactness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fixedWeight_chartCompactness

/-- info: 'FormalResearch.ModularBootstrap.FoldTip.fixedWeight_chartCompactness_limsup_ereal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fixedWeight_chartCompactness_limsup_ereal

/-- info: 'FormalResearch.ModularBootstrap.FoldTip.fixedWeight_chartCompactness_limsup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fixedWeight_chartCompactness_limsup

/-- info: 'FormalResearch.ModularBootstrap.FoldTip.fixedWeight_chartCompactness_profile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fixedWeight_chartCompactness_profile

/-- info: 'FormalResearch.ModularBootstrap.FoldTip.fixedWeight_chartCompactness_virasoro' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fixedWeight_chartCompactness_virasoro

/-- info: 'FormalResearch.ModularBootstrap.FoldTip.fixedWeight_chartCompactness_clark' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fixedWeight_chartCompactness_clark

end FormalResearch.ModularBootstrap.FoldTip
