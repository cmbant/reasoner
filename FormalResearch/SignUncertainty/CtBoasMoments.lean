module

public import Mathlib
public import FormalResearch.SignUncertainty.CtBandTop
public import FormalResearch.SignUncertainty.CtDyadicTaperBuild
public import FormalResearch.SignUncertainty.CtBoasFarField
public import FormalResearch.SignUncertainty.CtBoasNeg

/-!
# `ct:boas`, `ct:Bj-pointwise` (f): the band moments in the variable `L`, from the top scale

`constant_terms_lower.tex`, `ct:dyadic` (1) at the top scale `R_J`, in the form consumed by the field `e_moment` of `BoasInputs`
and by the taper estimate `trunc_lo`: with `h = hankelHL c f` (`h(L) dL = dm(ξ)`, `ξ = e^L/π²`), `v'(L) = -ũ(ξ(L)) = K g(L)`
(`ctVprime`) and `L_J = log(π² ξ(-R_J))` for a good radius `R_J ∈ [b²c^{2/3}, b²c^{2/3}+1]`, `b = 1/100`:

* `∫_{0 < L ≤ L_J} v'|h| ≤ (3 + K) c^{1/3}`  (the first moment, `R_J B₁(R_J)` plus `3·M[f]` below the threshold),
* `∫_{L > L_J} |h| ≤ K c^{-1/3}`  (the tail `B₂(R_J)`).

This needs only the top-scale bootstrap `hankel_top_moments`; no multiscale bootstrap: the moments at any smaller radius
`R' ≤ R_J` follow by Chebyshev (`v' ≥ R'` beyond `Λ`), see `CtBoasConcrete`.  **Proved**, unconditional.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.Special FormalResearch.TwoEdgeBootstrap FormalResearch.ModularBootstrap.ConcreteBootstrap

/-! ### Monotonicity of the chart on the disc `e^L - 1 ≤ 5·10⁻⁴` -/

lemma ctChartG_strictMonoOn {L₁ : ℝ} (hL₁ : Real.exp L₁ - 1 ≤ 5e-4) : StrictMonoOn ctChartG (Icc 0 L₁) := by
  have hd : ∀ x ∈ Icc 0 L₁, HasDerivAt ctChartG (-(ctYRD (Real.exp x - 1)) * Real.exp x) x := fun x hx =>
    ctChartG_hasDerivAt hx.1 (by linarith [Real.exp_le_exp.2 hx.2])
  refine strictMonoOn_of_deriv_pos (convex_Icc 0 L₁) (fun x hx => (hd x hx).continuousAt.continuousWithinAt) ?_
  intro x hx
  rw [interior_Icc] at hx
  rw [(hd x ⟨hx.1.le, hx.2.le⟩).deriv]
  have := (ctChartG_deriv_bounds hx.1.le (by linarith [Real.exp_le_exp.2 hx.2.le])).1
  nlinarith [Real.exp_pos x]

lemma ctChartG_continuousOn {L₁ : ℝ} (hL₁ : Real.exp L₁ - 1 ≤ 5e-4) : ContinuousOn ctChartG (Icc 0 L₁) :=
  fun x hx => (ctChartG_hasDerivAt hx.1 (by linarith [Real.exp_le_exp.2 hx.2])).continuousAt.continuousWithinAt

lemma ctVprime_strictMonoOn {c : ℝ} (hc : 0 < c) {L₁ : ℝ} (hL₁ : Real.exp L₁ - 1 ≤ 5e-4) :
    StrictMonoOn (ctVprime c) (Icc 0 L₁) := fun _ hx _ hy hxy =>
  mul_lt_mul_of_pos_left (ctChartG_strictMonoOn hL₁ hx hy hxy) (langerScale_pos hc)

lemma ctVprime_continuousOn {c : ℝ} {L₁ : ℝ} (hL₁ : Real.exp L₁ - 1 ≤ 5e-4) :
    ContinuousOn (ctVprime c) (Icc 0 L₁) :=
  continuousOn_const.mul (ctChartG_continuousOn hL₁)

lemma ctVprime_nonneg {c : ℝ} (hc : 0 < c) {L : ℝ} (hL0 : 0 ≤ L) (hL : Real.exp L - 1 ≤ 5e-4) :
    0 ≤ ctVprime c L :=
  mul_nonneg (langerScale_pos hc).le (by linarith [(ctChartG_bounds hL0 hL).1])

/-- `0.998 K L ≤ v'(L) ≤ 1.0025 K L` on the disc. -/
lemma ctVprime_bounds {c : ℝ} (hc : 0 < c) {L : ℝ} (hL0 : 0 ≤ L) (hL : Real.exp L - 1 ≤ 5e-4) :
    0.998 * langerScale c * L ≤ ctVprime c L ∧ ctVprime c L ≤ 1.0025 * langerScale c * L := by
  have hK := langerScale_pos hc
  have hb := ctChartG_bounds hL0 hL
  unfold ctVprime
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hb.1 hK.le]
  · nlinarith [mul_le_mul_of_nonneg_left hb.2.1 hK.le]

/-! ### The change of variables `ξ = e^L/π²` for `dm⁺` -/

/-- `∫ φ d(dm⁺) = ∫_ℝ φ(e^L/π²) max(h(L), 0) dL`. -/
lemma integral_dmPos_eq {c ε : ℝ} (hc : 0 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f) (φ : ℝ → ℝ) :
    ∫ ξ, φ ξ ∂hankelDmPos c f = ∫ L, φ (Real.exp L / π ^ 2) * max (hankelHL c f L) 0 := by
  rw [hankelDmPos_integral hc hf]
  have hpi : (0 : ℝ) < π ^ 2 := by positivity
  set ψ : ℝ → ℝ := fun L => Real.exp L / π ^ 2 with hψ
  have himg : ψ '' univ = Ioi 0 := by
    ext ξ
    simp only [mem_image, mem_univ, true_and, mem_Ioi, hψ]
    constructor
    · rintro ⟨L, rfl⟩; positivity
    · intro hξ
      refine ⟨Real.log (π ^ 2 * ξ), ?_⟩
      rw [Real.exp_log (by positivity)]; field_simp
  have hd : ∀ L ∈ (univ : Set ℝ), HasDerivWithinAt ψ (Real.exp L / π ^ 2) univ L :=
    fun L _ => ((Real.hasDerivAt_exp L).div_const _).hasDerivWithinAt
  have hinj : InjOn ψ univ := by
    intro a _ b _ hab
    simp only [hψ] at hab
    exact Real.exp_injective ((div_left_inj₀ hpi.ne').1 hab)
  have key := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ hd hinj
    (fun ξ => max (hankelDmDens c f ξ) 0 • φ ξ)
  rw [himg, setIntegral_univ] at key
  rw [key]
  refine integral_congr_ae (ae_of_all _ fun L => ?_)
  have hp : 0 < Real.exp L / π ^ 2 := by positivity
  have hdens : hankelDmDens c f (Real.exp L / π ^ 2) * (Real.exp L / π ^ 2) = hankelHL c f L := by
    unfold hankelDmDens hankelHL; ring
  simp only [smul_eq_mul, hψ]
  have e : max (hankelDmDens c f (Real.exp L / π ^ 2) * (Real.exp L / π ^ 2)) 0 =
      max (hankelDmDens c f (Real.exp L / π ^ 2)) 0 * (Real.exp L / π ^ 2) := by
    rw [max_mul_of_nonneg _ _ hp.le, zero_mul]
  rw [abs_of_pos hp, ← hdens, e]
  ring

/-- `B₁` in the variable `L`. -/
lemma hankelBootB1_eq {c ε : ℝ} (hc : 0 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f) (R u_T : ℝ) :
    hankelBootB1 c f R u_T = R⁻¹ * ∫ L, (Icc (hankelXi c u_T) (hankelXi c (-R))).indicator
      (fun ξ => -hankelBandU c ξ) (Real.exp L / π ^ 2) * max (hankelHL c f L) 0 := by
  unfold hankelBootB1
  rw [← integral_indicator measurableSet_Icc, integral_dmPos_eq hc hf]

/-- `B₂` in the variable `L`. -/
lemma hankelBootB2_eq {c ε : ℝ} (hc : 0 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f) (R : ℝ) :
    hankelBootB2 c f R = ∫ L, (Ici (hankelXi c (-R))).indicator (fun _ => (1 : ℝ)) (Real.exp L / π ^ 2) *
      max (hankelHL c f L) 0 := by
  unfold hankelBootB2
  have := isFiniteMeasure_hankelDmPos hc hf
  have h1 : (hankelDmPos c f (Ici (hankelXi c (-R)))).toReal =
      ∫ ξ, (Ici (hankelXi c (-R))).indicator (fun _ => (1 : ℝ)) ξ ∂hankelDmPos c f := by
    rw [integral_indicator_const _ measurableSet_Ici]
    simp [Measure.real]
  rw [h1, integral_dmPos_eq hc hf]

lemma ctVprime_eq_neg_bandU (c L : ℝ) : ctVprime c L = -hankelBandU c (Real.exp L / π ^ 2) := by
  have : π ^ 2 * (Real.exp L / π ^ 2) - 1 = Real.exp L - 1 := by
    have : π ^ 2 ≠ 0 := by positivity
    field_simp
  rw [hankelBandU_eq, this]
  unfold ctVprime ctChartG; ring

/-- `R·B₁` in the variable `L`: the first band moment of `h` over `[L_t, L_J]` (`L_t = L(ξ(u_T))`, `L_J = L(ξ(-R))`),
valid when `π²ξ(u_T) , π²ξ(-R) > 0`. -/
lemma hankelBootB1_mul_eq {c ε : ℝ} (hc : 0 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f) {R u_T : ℝ} (hR : 0 < R)
    (hu : 0 < π ^ 2 * hankelXi c u_T) (hr : 0 < π ^ 2 * hankelXi c (-R)) :
    R * hankelBootB1 c f R u_T = ∫ L, (Icc (Real.log (π ^ 2 * hankelXi c u_T))
      (Real.log (π ^ 2 * hankelXi c (-R)))).indicator (fun L => ctVprime c L * max (hankelHL c f L) 0) L := by
  rw [hankelBootB1_eq hc hf, ← mul_assoc, mul_inv_cancel₀ hR.ne', one_mul]
  refine integral_congr_ae (ae_of_all _ fun L => ?_)
  have hmem : Real.exp L / π ^ 2 ∈ Icc (hankelXi c u_T) (hankelXi c (-R)) ↔
      L ∈ Icc (Real.log (π ^ 2 * hankelXi c u_T)) (Real.log (π ^ 2 * hankelXi c (-R))) := by
    have hpi : (0 : ℝ) < π ^ 2 := by positivity
    rw [mem_Icc, mem_Icc, Real.log_le_iff_le_exp hu, Real.le_log_iff_exp_le hr,
      le_div_iff₀ hpi, div_le_iff₀ hpi, mul_comm, mul_comm (hankelXi c (-R))]
  beta_reduce
  by_cases hL : L ∈ Icc (Real.log (π ^ 2 * hankelXi c u_T)) (Real.log (π ^ 2 * hankelXi c (-R)))
  · rw [indicator_of_mem hL, indicator_of_mem (hmem.2 hL), ← ctVprime_eq_neg_bandU]
  · rw [indicator_of_notMem hL, indicator_of_notMem (fun h => hL (hmem.1 h))]
    simp

/-- **Top-scale band moments in the variable `L`** (`ct:dyadic` (1) at `r = R_J`, in the form used by `ct:Bj-pointwise` (f) and the
taper estimate): for `c ≥ c₀`, a feasible `f` with `M[f] = 1` and `T < cξ(a₁)` there is `L_J > 0` with `e^{L_J} - 1 ≤ 5·10⁻⁴` and
`v'(L_J) = R_J ∈ [b²c^{2/3}, b²c^{2/3} + 1]` (`b = 1/100`, a good radius) such that
`∫_{0 < L ≤ L_J} v'|h| ≤ K c^{1/3}` and `∫_{L > L_J} |h| ≤ K c^{-1/3}`. -/
theorem ct_boas_moments_top : ∃ K c₀ : ℝ, 0 ≤ K ∧ ∀ (c ε T : ℝ) (f : ℝ → ℝ), c₀ ≤ c →
    IsHankelFeasible c ε T f → (ε = 1 ∨ ε = -1) → hankelMass c f = 1 →
    T < c * hankelXi c (airyZero 1) →
    ∃ LJ : ℝ, 0 < LJ ∧ Real.exp LJ - 1 ≤ 5e-4 ∧
      (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) ≤ ctVprime c LJ ∧
      ctVprime c LJ ≤ (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) + 1 ∧
      (∫ L in Ioc 0 LJ, ctVprime c L * |hankelHL c f L|) ≤ K * c ^ (1 / 3 : ℝ) ∧
      (∫ L in Ioi LJ, |hankelHL c f L|) ≤ K * c ^ (-(1 / 3 : ℝ)) := by
  obtain ⟨K₀, cK, hK0, hK⟩ := hankel_top_moments
  obtain ⟨c₁q, hc₁q, hquant⟩ := hankel_quantC1_of_feasible
  refine ⟨K₀ + 3, max (max 1e14 cK) c₁q, by linarith, ?_⟩
  intro c ε T f hc hf hε hmass hviol
  have hc14 : 1e14 ≤ c := (((le_max_left _ _).trans (le_max_left _ _))).trans hc
  have hcK : cK ≤ c := ((le_max_right _ _).trans (le_max_left _ _)).trans hc
  have hcq : c₁q ≤ c := (le_max_right _ _).trans hc
  have hc0 : 0 < c := by linarith
  have hc3 : 3e6 ≤ c := by linarith
  obtain ⟨u_T, ha1, -, hT, hB2⟩ := hquant c ε T f hcq hf hε hmass hviol
  obtain ⟨hu0, hu3⟩ := hankelBoot_uT_range ha1 hB2
  have h48 : 48 ≤ (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) := by
    obtain ⟨t, ht14, hct, hk4, hK8, -⟩ := hankel_window_cnum hc14
    rw [hK8]
    have : (14 : ℝ) ^ 8 ≤ t ^ 8 := pow_le_pow_left₀ (by norm_num) ht14 8
    norm_num at this ⊢
    linarith
  obtain ⟨R, hR1, hR2, hgood⟩ := hankelBoot_good_circle_window ((1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ)) (by linarith)
  obtain ⟨hR48, hRA1, -, hRc⟩ := hankelBoot_radius_facts hc3 h48 hR1 hR2
  have hR0 : 0 < R := by linarith
  have hBK := hK c ε T u_T R f hcK hf hε hmass hT ha1 hB2 hR1 hR2 hgood
  have hfe := hf.toIsHankelEigenfn
  have hAu : |u_T| ≤ langerRadius c := by
    rw [abs_of_nonpos hu0]; linarith [(hankel_radius_ge hc3).1]
  have hAR : |(-R)| ≤ langerRadius c := by rw [abs_neg, abs_of_pos hR0]; linarith
  -- the band edge `L_J`
  obtain ⟨hLJ0, hLJe, hLJv⟩ := hankel_band_edge hc0 hR0 (by linarith)
  set LJ := Real.log (π ^ 2 * hankelXi c (-R)) with hLJdef
  -- the threshold `L_t`
  obtain ⟨hw0, hw1, -⟩ := hankelXi_w_bounds hc0 hAu hu0
  obtain ⟨hwr0, -, -⟩ := hankelXi_w_bounds hc0 hAR (by linarith)
  have hpu : 0 < π ^ 2 * hankelXi c u_T := by linarith
  have hpr : 0 < π ^ 2 * hankelXi c (-R) := by linarith
  set Lt := Real.log (π ^ 2 * hankelXi c u_T) with hLtdef
  have hexpLt : Real.exp Lt = π ^ 2 * hankelXi c u_T := Real.exp_log hpu
  have hLt0 : 0 ≤ Lt := Real.log_nonneg (by linarith)
  have hLte : Real.exp Lt - 1 ≤ 5e-4 := by rw [hexpLt]; linarith
  have hvt : ctVprime c Lt = -u_T := by
    rw [ctVprime_eq_neg_bandU]
    have : Real.exp Lt / π ^ 2 = hankelXi c u_T := by rw [hexpLt]; field_simp
    rw [this, hankelBandU_hankelXi hc0 hAu]
  have hLtJ : Lt ≤ LJ := by
    by_contra hcon
    rw [not_le] at hcon
    have := ctVprime_strictMonoOn hc0 hLte ⟨hLJ0.le, hcon.le⟩ ⟨hLt0, le_rfl⟩ hcon
    rw [hLJv, hvt] at this
    linarith
  -- `h ≥ 0` above `L_t`
  have hpos : ∀ L, Lt ≤ L → 0 ≤ hankelHL c f L := by
    intro L hL
    refine hankelHL_nonneg_of_tail hc0 hf ?_
    have h1 : Real.exp Lt ≤ Real.exp L := Real.exp_le_exp.2 hL
    rw [hexpLt] at h1
    have h2 : hankelXi c u_T ≤ Real.exp L / π ^ 2 := by
      rw [le_div_iff₀ (by positivity)]; linarith
    rw [← hT]
    exact mul_le_mul_of_nonneg_left h2 hc0.le
  have hhint := integrable_hankelHL hc0 hfe
  have hmass1 : ∫ L, |hankelHL c f L| = 1 := by rw [integral_abs_hankelHL hc0 hfe, hmass]
  refine ⟨LJ, hLJ0, hLJe, by rw [hLJv]; exact hR1, by rw [hLJv]; exact hR2, ?_, ?_⟩
  · -- first moment
    set G1 : ℝ → ℝ := (Icc Lt LJ).indicator (fun L => ctVprime c L * max (hankelHL c f L) 0) with hG1
    have hG1int : Integrable G1 := by
      refine (integrable_indicator_iff measurableSet_Icc).2 ?_
      have hmaxint : IntegrableOn (fun L => max (hankelHL c f L) 0) (Icc Lt LJ) :=
        (hhint.sup (integrable_zero ℝ ℝ volume)).integrableOn
      have hcont : ContinuousOn (ctVprime c) (Icc Lt LJ) :=
        (ctVprime_continuousOn hLJe).mono (Icc_subset_Icc_left hLt0)
      exact (hmaxint.mul_continuousOn hcont isCompact_Icc).congr_fun (fun L _ => mul_comm _ _) measurableSet_Icc
    have hG10 : ∀ L, 0 ≤ G1 L := by
      intro L
      rw [hG1]
      refine indicator_nonneg (fun L hL => ?_) L
      exact mul_nonneg (ctVprime_nonneg hc0 (hLt0.trans hL.1)
        (by linarith [Real.exp_le_exp.2 hL.2])) (le_max_right _ _)
    have hB1 := hankelBootB1_mul_eq hc0 hfe hR0 hpu hpr
    rw [← hLtdef, ← hLJdef, ← hG1] at hB1
    have hRB : R * hankelBootB1 c f R u_T ≤ K₀ * c ^ (1 / 3 : ℝ) := by
      have hB1le : hankelBootB1 c f R u_T ≤ K₀ * c ^ (-(1 / 3 : ℝ)) := by
        have := hankelBootB2_nonneg c f R
        linarith
      have hcc : R * (K₀ * c ^ (-(1 / 3 : ℝ))) ≤ c ^ (2 / 3 : ℝ) * (K₀ * c ^ (-(1 / 3 : ℝ))) :=
        mul_le_mul_of_nonneg_right hRc (by positivity)
      have : c ^ (2 / 3 : ℝ) * (K₀ * c ^ (-(1 / 3 : ℝ))) = K₀ * c ^ (1 / 3 : ℝ) := by
        rw [mul_left_comm, ← Real.rpow_add hc0]; norm_num
      nlinarith [mul_le_mul_of_nonneg_left hB1le hR0.le]
    have hc13 : 1 ≤ c ^ (1 / 3 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
    have hpt : ∀ L ∈ Ioc 0 LJ, ctVprime c L * |hankelHL c f L| ≤ 3 * |hankelHL c f L| + G1 L := by
      intro L hL
      have habs := abs_nonneg (hankelHL c f L)
      by_cases hLt : L ≤ Lt
      · have hv : ctVprime c L ≤ 3 := by
          have := (ctVprime_strictMonoOn hc0 hLte).monotoneOn ⟨hL.1.le, hLt⟩ ⟨hLt0, le_rfl⟩ hLt
          rw [hvt] at this; linarith
        have := mul_le_mul_of_nonneg_right hv habs
        linarith [hG10 L]
      · rw [not_le] at hLt
        have hLm : L ∈ Icc Lt LJ := ⟨hLt.le, hL.2⟩
        rw [hG1, indicator_of_mem hLm, abs_of_nonneg (hpos L hLt.le), max_eq_left (hpos L hLt.le)]
        linarith [hpos L hLt.le]
    have hnn : ∀ L ∈ Ioc 0 LJ, 0 ≤ ctVprime c L * |hankelHL c f L| := by
      intro L hL
      exact mul_nonneg (ctVprime_nonneg hc0 hL.1.le (by linarith [Real.exp_le_exp.2 hL.2])) (abs_nonneg _)
    have hrint : Integrable fun L => 3 * |hankelHL c f L| + G1 L := (hhint.abs.const_mul 3).add hG1int
    calc ∫ L in Ioc 0 LJ, ctVprime c L * |hankelHL c f L|
        ≤ ∫ L in Ioc 0 LJ, (3 * |hankelHL c f L| + G1 L) := by
          refine integral_mono_of_nonneg ((ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ hnn))
            hrint.integrableOn ((ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ hpt))
      _ ≤ ∫ L, (3 * |hankelHL c f L| + G1 L) :=
          setIntegral_le_integral hrint (ae_of_all _ fun L => by
            show 0 ≤ 3 * |hankelHL c f L| + G1 L
            have := hG10 L; have := abs_nonneg (hankelHL c f L); linarith)
      _ = 3 * 1 + R * hankelBootB1 c f R u_T := by
          rw [integral_add (hhint.abs.const_mul 3) hG1int, integral_const_mul, hmass1, hB1]
      _ ≤ (K₀ + 3) * c ^ (1 / 3 : ℝ) := by nlinarith
  · -- tail
    have hg2int : Integrable fun L => (Ici (hankelXi c (-R))).indicator (fun _ => (1 : ℝ)) (Real.exp L / π ^ 2) *
        max (hankelHL c f L) 0 := by
      have hm1 : Measurable fun L : ℝ => (Ici (hankelXi c (-R))).indicator (fun _ => (1 : ℝ)) (Real.exp L / π ^ 2) :=
        (measurable_const.indicator measurableSet_Ici).comp (Real.measurable_exp.div_const _)
      refine hhint.abs.mono' (hm1.aestronglyMeasurable.mul
        (hhint.aestronglyMeasurable.sup aestronglyMeasurable_const)) (ae_of_all _ fun L => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      have h1 : |(Ici (hankelXi c (-R))).indicator (fun _ => (1 : ℝ)) (Real.exp L / π ^ 2)| ≤ 1 := by
        by_cases hx : Real.exp L / π ^ 2 ∈ Ici (hankelXi c (-R))
        · rw [indicator_of_mem hx]; simp
        · rw [indicator_of_notMem hx]; simp
      have h2 : |max (hankelHL c f L) 0| ≤ |hankelHL c f L| := by
        rcases le_total (hankelHL c f L) 0 with h | h
        · rw [max_eq_right h, abs_zero]; exact abs_nonneg _
        · rw [max_eq_left h]
      calc _ ≤ 1 * |hankelHL c f L| := mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
        _ = _ := one_mul _
    have hB2 := hankelBootB2_eq hc0 hfe R
    have hpt : ∀ L ∈ Ioi LJ, |hankelHL c f L| ≤ (Ici (hankelXi c (-R))).indicator (fun _ => (1 : ℝ))
        (Real.exp L / π ^ 2) * max (hankelHL c f L) 0 := by
      intro L hL
      have hLt : Lt ≤ L := hLtJ.trans (le_of_lt hL)
      have hx : Real.exp L / π ^ 2 ∈ Ici (hankelXi c (-R)) := by
        have h1 : Real.exp LJ ≤ Real.exp L := Real.exp_le_exp.2 (le_of_lt hL)
        rw [hLJdef, Real.exp_log hpr] at h1
        show hankelXi c (-R) ≤ Real.exp L / π ^ 2
        rw [le_div_iff₀ (by positivity)]; linarith
      rw [indicator_of_mem hx, abs_of_nonneg (hpos L hLt), max_eq_left (hpos L hLt)]; ring_nf; rfl
    have hc13 : 0 < c ^ (-(1 / 3 : ℝ)) := Real.rpow_pos_of_pos hc0 _
    calc ∫ L in Ioi LJ, |hankelHL c f L|
        ≤ ∫ L, (Ici (hankelXi c (-R))).indicator (fun _ => (1 : ℝ)) (Real.exp L / π ^ 2) *
            max (hankelHL c f L) 0 := by
          calc ∫ L in Ioi LJ, |hankelHL c f L|
              ≤ ∫ L in Ioi LJ, (Ici (hankelXi c (-R))).indicator (fun _ => (1 : ℝ)) (Real.exp L / π ^ 2) *
                  max (hankelHL c f L) 0 :=
                setIntegral_mono_on hhint.abs.integrableOn hg2int.integrableOn measurableSet_Ioi hpt
            _ ≤ _ := setIntegral_le_integral hg2int (ae_of_all _ fun L => by
                refine mul_nonneg ?_ (le_max_right _ _)
                exact indicator_nonneg (fun _ _ => zero_le_one) _)
      _ = hankelBootB2 c f R := hB2.symm
      _ ≤ K₀ * c ^ (-(1 / 3 : ℝ)) := by
          have := hankelBootB1_nonneg hc3 hf hε hmass hT hu0 hu3 hR0 (by linarith) (by linarith)
          linarith
      _ ≤ (K₀ + 3) * c ^ (-(1 / 3 : ℝ)) := mul_le_mul_of_nonneg_right (by linarith) hc13.le

/-- info: 'FormalResearch.SignUncertainty.ct_boas_moments_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ct_boas_moments_top

end FormalResearch.SignUncertainty
