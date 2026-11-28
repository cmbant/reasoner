module

public import FormalResearch.SignUncertainty.CeHankelDefs
public import FormalResearch.SignUncertainty.CtOuterParam
public import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Nonvanishing of the negative projection `g - h` (`general_theorems.tex`, `thm:ct-upper` (i))

For real `c > 1/2` and any feasible Cohn--Elkies Hankel pair `(h, g)` (`IsHankelCEFeasible c T h g`),
`(g - h)/2` cannot vanish identically on `[0, ∞)`: otherwise `h = g ≥ 0` vanishes on `[T, ∞)`,
so `besselHankelTransform c h` extends via `Complex.regularizedHGFun 0 {c}` to an entire function
vanishing on `[T, ∞)`, hence identically, giving `g 0 = h 0 = 0`, contradicting `0 < g 0`.

Headline theorem:
* `ce_nonzero_neg`: discharges the `CtUpperCEInputs.ce_nonzero_neg` field.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.Special

/-- Complexified Hankel kernel `z ↦ Γ(c) · ₀F₁-regularized(c; -4π² s z)` agreeing with `hankelKernel c Δ s`
for `Δ ≥ 0`, `s ≥ 0`. -/
private noncomputable def hankelKernelC (c : ℝ) (z : ℂ) (s : ℝ) : ℂ :=
  (Real.Gamma c : ℂ) * Complex.regularizedHGFun 0 {(c : ℂ)} (-((4 * π ^ 2 * s : ℝ) : ℂ) * z)

private lemma hankelKernelC_ofReal {c Δ s : ℝ} (hΔ : 0 ≤ Δ) (hs : 0 ≤ s) :
    hankelKernelC c (Δ : ℂ) s = (hankelKernel c Δ s : ℂ) := by
  unfold hankelKernel hankelPhi hankelKernelC
  rw [besselNorm_ofReal_eq (c - 1) (4 * π * √(Δ * s))]
  have hcm1 : c - 1 + 1 = c := by ring
  have harg : -(((4 * π * √(Δ * s) : ℝ) : ℂ) / 2) ^ 2 = -((4 * π ^ 2 * s : ℝ) : ℂ) * (Δ : ℂ) := by
    have hsq : √(Δ * s) ^ 2 = Δ * s := Real.sq_sqrt (mul_nonneg hΔ hs)
    norm_cast
    calc -((4 * π * √(Δ * s)) / 2) ^ 2 = -(4 * π ^ 2 * √(Δ * s) ^ 2) := by ring
      _ = -(4 * π ^ 2 * (Δ * s)) := by rw [hsq]
      _ = -(4 * π ^ 2 * s) * Δ := by ring
  rw [show ((c - 1 : ℝ) : ℂ) + 1 = (c : ℂ) by push_cast; ring, hcm1, harg]

private lemma hankelKernelC_continuous (c : ℝ) :
    Continuous (fun p : ℂ × ℝ => hankelKernelC c p.1 p.2) := by
  have hc : Continuous fun z : ℂ => Complex.regularizedHGFun 0 {(c : ℂ)} z :=
    continuous_iff_continuousAt.mpr fun z =>
      (Complex.analyticAt_regularizedHGFun_zero z).continuousAt
  refine continuous_const.mul (hc.comp ?_)
  exact (Complex.continuous_ofReal.comp (continuous_const.mul continuous_snd)).neg.mul continuous_fst

/-- **`ce_nonzero_neg`** (`general_theorems.tex`, proof of `thm:ct-upper` (i)): for real `c > 1/2` and any
feasible Cohn--Elkies Hankel pair `(h, g)` at `T`, there exists `Δ ≥ 0` with `g Δ - h Δ ≠ 0`. -/
theorem ce_nonzero_neg {c T : ℝ} {h g : ℝ → ℝ} (hc : 1 / 2 < c) (H : IsHankelCEFeasible c T h g) :
    ∃ Δ : ℝ, 0 ≤ Δ ∧ g Δ - h Δ ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hgh : ∀ Δ : ℝ, 0 ≤ Δ → g Δ = h Δ := fun Δ hΔ => sub_eq_zero.mp (hcon Δ hΔ)
  have hzero_tail : ∀ s : ℝ, T ≤ s → h s = 0 := fun s hs => by
    have hs0 : 0 ≤ s := le_trans H.T_nonneg hs
    exact le_antisymm (H.h_tail s hs) (by rw [← hgh s hs0]; exact H.g_nonneg s hs0)
  let F : ℂ → ℂ := fun z => ∫ s in Ioc (0 : ℝ) T, ((h s * hankelRho0 c s : ℝ) : ℂ) * hankelKernelC c z s
  have hF_diff : DifferentiableOn ℂ F univ := by
    refine CtOuter.differentiableOn_integral_param (μ := volume.restrict (Ioc (0 : ℝ) T))
      (Φ := fun z s => ((h s * hankelRho0 c s : ℝ) : ℂ) * hankelKernelC c z s) isOpen_univ ?_ ?_ ?_
    · intro z _
      have hm1 : AEStronglyMeasurable (fun s => ((h s * hankelRho0 c s : ℝ) : ℂ))
          (volume.restrict (Ioc (0 : ℝ) T)) :=
        Complex.continuous_ofReal.comp_aestronglyMeasurable
          (H.h_int.aestronglyMeasurable.mono_measure (Measure.restrict_mono Ioc_subset_Ioi_self le_rfl))
      have hm2 : AEStronglyMeasurable (fun s => hankelKernelC c z s)
          (volume.restrict (Ioc (0 : ℝ) T)) :=
        ((hankelKernelC_continuous c).comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
      exact hm1.mul hm2
    · refine ae_of_all _ fun s => (Differentiable.differentiableOn ?_)
      refine differentiable_const _ |>.mul ?_
      refine differentiable_const _ |>.mul ?_
      intro z
      exact (Complex.analyticAt_regularizedHGFun_zero _).differentiableAt.comp z
        ((differentiableAt_const _).mul differentiableAt_id)
    · intro z₀ _
      have hc_comp : IsCompact (closedBall z₀ 1 ×ˢ Icc (0 : ℝ) T) :=
        (isCompact_closedBall z₀ 1).prod isCompact_Icc
      obtain ⟨M, hM⟩ := hc_comp.exists_bound_of_continuousOn
        (hankelKernelC_continuous c).continuousOn
      have hM_nn : 0 ≤ M := le_trans (norm_nonneg _)
        (hM (z₀, 0) ⟨mem_closedBall_self zero_le_one, left_mem_Icc.mpr H.T_nonneg⟩)
      have hb_int : Integrable (fun s => |h s * hankelRho0 c s| * M)
          (volume.restrict (Ioc (0 : ℝ) T)) :=
        (H.h_int.mono_set Ioc_subset_Ioi_self).norm.mul_const M
      refine ⟨1, one_pos, fun s => |h s * hankelRho0 c s| * M, hb_int, ?_⟩
      rw [ae_restrict_iff' measurableSet_Ioc]
      refine ae_of_all _ fun s hs z hz => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left
        (hM (z, s) ⟨ball_subset_closedBall hz, Ioc_subset_Icc_self hs⟩) (abs_nonneg _)
  have hF_real : ∀ Δ : ℝ, 0 ≤ Δ → F (Δ : ℂ) = (besselHankelTransform c h Δ : ℂ) := by
    intro Δ hΔ
    have hsplit : Ioc (0 : ℝ) T ∪ Ioi T = Ioi (0 : ℝ) := Ioc_union_Ioi_eq_Ioi H.T_nonneg
    have hI_split : ∫ s in Ioi (0 : ℝ), h s * hankelRho0 c s * hankelKernel c Δ s =
        ∫ s in Ioc (0 : ℝ) T, h s * hankelRho0 c s * hankelKernel c Δ s := by
      have hint_all := integrableOn_mul_hankelKernel hc H.h_int Δ
      rw [← hsplit, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
        (hint_all.mono_set Ioc_subset_Ioi_self) (hint_all.mono_set (Ioi_subset_Ioi H.T_nonneg))]
      have hvan : ∫ s in Ioi T, h s * hankelRho0 c s * hankelKernel c Δ s = 0 := by
        refine setIntegral_eq_zero_of_forall_eq_zero fun s (hs : T < s) => ?_
        rw [hzero_tail s hs.le, zero_mul, zero_mul]
      rw [hvan, add_zero]
    unfold besselHankelTransform
    rw [hI_split, ← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
    rw [hankelKernelC_ofReal hΔ hs.1.le, ← Complex.ofReal_mul]
  have hF_zero_ray : ∀ Δ : ℝ, T ≤ Δ → F (Δ : ℂ) = 0 := fun Δ hΔ => by
    have hΔ0 : 0 ≤ Δ := le_trans H.T_nonneg hΔ
    rw [hF_real Δ hΔ0, H.g_eq Δ (mem_Ici.2 hΔ0), hgh Δ hΔ0, hzero_tail Δ hΔ, Complex.ofReal_zero]
  have hFan : AnalyticOnNhd ℂ F univ := hF_diff.analyticOnNhd isOpen_univ
  have hfreq : ∃ᶠ z in 𝓝[≠] (T : ℂ), F z = 0 := by
    have htend : Tendsto (fun n : ℕ => ((T + (((n + 1 : ℕ) : ℝ))⁻¹ : ℝ) : ℂ)) atTop (𝓝[≠] (T : ℂ)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, Eventually.of_forall fun n => ?_⟩
      · have h0 : Tendsto (fun n : ℕ => T + (((n + 1 : ℕ) : ℝ))⁻¹) atTop (𝓝 (T + 0)) :=
          tendsto_const_nhds.add (tendsto_inv_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1))
        rw [add_zero] at h0
        exact Complex.continuous_ofReal.continuousAt.tendsto.comp h0
      · simp only [mem_compl_iff, mem_singleton_iff, Complex.ofReal_inj]
        linarith [show (0 : ℝ) < (((n + 1 : ℕ) : ℝ))⁻¹ by positivity]
    exact htend.frequently (Eventually.of_forall fun n =>
      hF_zero_ray _ (by linarith [show (0 : ℝ) < (((n + 1 : ℕ) : ℝ))⁻¹ by positivity])).frequently
  have hF_id : ∀ z : ℂ, F z = 0 := fun z =>
    hFan.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ (mem_univ (T : ℂ)) hfreq
      (mem_univ z)
  have h0 : g 0 = 0 := by
    have h := hF_id 0
    rw [← Complex.ofReal_zero, hF_real 0 le_rfl, H.g_eq 0 (mem_Ici.2 le_rfl)] at h
    exact Complex.ofReal_eq_zero.mp h
  linarith [H.pos]

/-- info: 'FormalResearch.SignUncertainty.ce_nonzero_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ce_nonzero_neg

end FormalResearch.SignUncertainty
