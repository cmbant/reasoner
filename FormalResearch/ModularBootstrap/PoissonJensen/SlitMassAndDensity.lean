module

public import FormalResearch.ModularBootstrap.PoissonJensen.HankelInversion
public import FormalResearch.ModularBootstrap.PoissonJensen.HalfPlaneJensen
public import FormalResearch.ModularBootstrap.PoissonJensen.HarmonicMajorant
public import FormalResearch.ModularBootstrap.SlitStrip.RealSlice
public import FormalResearch.ModularBootstrap.SlitStrip.EntropyAndDeficit
public import FormalResearch.ModularBootstrap.Bessel.VCorollaries
public import FormalResearch.ModularBootstrap.Crossing.BesselBridge
public import FormalResearch.ModularBootstrap.Integration.StripKernel
public import FormalResearch.ModularBootstrap.Crossing.LemmaInputs
public import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Slit mass bound, slit harmonic-measure pullback, and a.e. nonvanishing

Prepares all remaining analytic ingredients for `LemmaPJInput realSliceData`:

1. `hankelContinuation_neg` and `hankelContinuation_bdy_ne_zero_ae`: evenness of `G` and
   a.e. nonvanishing of `σ ↦ G(slitBoundaryMap σ)` on `slitPreimage` (isolated-zeros principle +
   `≤ 2` preimages per boundary point).
2. `eSlitMass`: `(eSlitMass)` from `lower_o1_two_edge.tex` (`vlo:eSlitMass`),
   `∫_{ξ_*}^∞ |g(c'x²/3)| K_a(c'x²/3) dx ≤ C_slit c'⁻¹ M[g]` for `c' ≥ 10000`.
3. Slit pullback change of variables relating `poissonKernel x y σ` on `slitPreimage` to
   `rightSlitDensity` / `leftSlitDensity` and Lebesgue integrals over `Ioi xiStar`, together with
   integrability of `log (slitDensity x y σ) * poissonKernel x y σ`.
-/

@[expose] public section

open Real Complex MeasureTheory Set Filter Topology
open scoped Interval

namespace FormalResearch.ModularBootstrap.PoissonJensen

open Crossing Integration Bessel

/-! ### 1. Evenness of `hankelContinuation` and a.e. nonvanishing on `slitPreimage` -/

lemma besselI0C_neg (z : ℂ) : besselI0C (-z) = besselI0C z := by
  unfold besselI0C
  congr 1
  have hsub := intervalIntegral.integral_comp_sub_left
    (fun θ : ℝ => Complex.exp (z * (Real.cos θ : ℝ))) π (a := 0) (b := π)
  simp only [sub_zero, sub_self] at hsub
  refine (intervalIntegral.integral_congr fun θ _ => ?_).trans hsub
  rw [Real.cos_pi_sub, Complex.ofReal_neg]
  congr 1
  ring

theorem hankelContinuation_neg (c' : ℝ) (g : ℝ → ℝ) (b : ℂ) :
    hankelContinuation c' g (-b) = hankelContinuation c' g b := by
  unfold hankelContinuation
  congr 2
  ext t
  congr 1
  rw [show 4 * (π : ℂ) * Complex.I * -b * (Real.sqrt (c' * t / 3) : ℝ) =
      -(4 * (π : ℂ) * Complex.I * b * (Real.sqrt (c' * t / 3) : ℝ)) by ring, besselI0C_neg]

lemma slitBoundaryMap_pos_quotient {σ : ℝ} (hσ : σ ∈ slitPreimage) :
    0 < (1 - σ) / (-σ * (1 + σ)) := by
  rcases hσ with ⟨hm1, h0⟩ | h1
  · exact div_pos (by linarith) (mul_pos (by linarith) (by linarith))
  · have hgt : 1 < σ := h1
    exact div_pos_of_neg_of_neg (by linarith) (mul_neg_of_neg_of_pos (by linarith) (by linarith))

lemma slitBoundaryMap_preimage_finite (r : ℝ) :
    {σ : ℝ | σ ∈ slitPreimage ∧ slitBoundaryMap σ = r}.Finite := by
  set E : ℝ := Real.exp (2 * π * r)
  have hE : 0 < E := Real.exp_pos _
  set s : ℝ := Real.sqrt (max ((E - 1) ^ 2 - 4 * E) 0)
  have hfin : ({(-(E - 1) + s) / (2 * E), (-(E - 1) - s) / (2 * E)} : Set ℝ).Finite :=
    (Set.finite_singleton _).insert _
  refine hfin.subset fun σ ⟨hσ, hr⟩ => ?_
  have hq : 0 < (1 - σ) / (-σ * (1 + σ)) := slitBoundaryMap_pos_quotient hσ
  have hden : -σ * (1 + σ) ≠ 0 := by
    rcases hσ with ⟨hm1, h0⟩ | h1
    · exact mul_ne_zero (by linarith) (by linarith)
    · have hgt : 1 < σ := h1
      exact mul_ne_zero (by linarith) (by linarith)
  have hlog : Real.log ((1 - σ) / (-σ * (1 + σ))) = 2 * π * r := by
    unfold slitBoundaryMap at hr
    have hpi : (2 * π : ℝ) ≠ 0 := by positivity
    calc Real.log ((1 - σ) / (-σ * (1 + σ)))
        = (2 * π) * ((2 * π)⁻¹ * Real.log ((1 - σ) / (-σ * (1 + σ)))) := by field_simp [hpi]
      _ = 2 * π * r := by rw [hr]
  have heq_E : (1 - σ) / (-σ * (1 + σ)) = E := by
    rw [← Real.exp_log hq, hlog]
  have hquad : E * σ ^ 2 + (E - 1) * σ + 1 = 0 := by
    have h1 : 1 - σ = E * (-σ * (1 + σ)) := (div_eq_iff hden).mp heq_E
    linarith
  have hsq : (2 * E * σ + (E - 1)) ^ 2 = (E - 1) ^ 2 - 4 * E := by
    nlinarith [hquad]
  have hmax : (E - 1) ^ 2 - 4 * E = s ^ 2 := by
    have hnn : 0 ≤ (E - 1) ^ 2 - 4 * E := by nlinarith [sq_nonneg (2 * E * σ + (E - 1))]
    dsimp [s]
    rw [max_eq_left hnn, Real.sq_sqrt hnn]
  rw [hmax] at hsq
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
  · left; field_simp [hE.ne']; linarith
  · right; rw [Set.mem_singleton_iff]; field_simp [hE.ne']; linarith

theorem hankelContinuation_bdy_ne_zero_ae {c' : ℝ} (hc : 1000 ≤ c') {g : ℝ → ℝ}
    (hg : TestClass virasoroProblem (c' / 12) g) {x : ℝ} (_hx : x ∈ Ico 0 xiStar)
    (hx_ne : g (c' * x ^ 2 / 3) ≠ 0) :
    ∀ᵐ σ ∂(volume.restrict slitPreimage),
      hankelContinuation c' g (slitBoundaryMap σ : ℂ) ≠ 0 := by
  have hc0 : 0 < c' := by linarith
  have han : AnalyticOnNhd ℂ (hankelContinuation c' g) {b : ℂ | |b.im| < 1 / 2} :=
    analyticOnNhd_hankelContinuation hc hg
  have hconv : Convex ℝ {b : ℂ | |b.im| < 1 / 2} := by
    have heq : {b : ℂ | |b.im| < 1 / 2} = Complex.imCLM ⁻¹' Ioo (-(1 / 2)) (1 / 2) := by
      ext b; simp [Complex.imCLM_apply, abs_lt]
    rw [heq]
    exact (convex_Ioo _ _).linear_preimage Complex.imCLM.toLinearMap
  have hpre : IsPreconnected {b : ℂ | |b.im| < 1 / 2} := hconv.isPreconnected
  have hz_re_cnt : {r : ℝ | hankelContinuation c' g (r : ℂ) = 0}.Countable := by
    have heq : {r : ℝ | hankelContinuation c' g (r : ℂ) = 0} =
        ⋃ n : ℕ, {r : ℝ | r ∈ Icc (-(n : ℝ)) n ∧ hankelContinuation c' g (r : ℂ) = 0} := by
      ext r
      simp only [Set.mem_ofPred_eq, mem_iUnion, mem_Icc]
      refine ⟨fun hr => ?_, fun ⟨_, _, hr⟩ => hr⟩
      obtain ⟨n, hn⟩ := exists_nat_ge |r|
      exact ⟨n, ⟨by linarith [abs_le.mp hn], by linarith [abs_le.mp hn]⟩, hr⟩
    rw [heq]
    have hfin : ∀ n : ℕ,
        {r : ℝ | r ∈ Icc (-(n : ℝ)) n ∧ hankelContinuation c' g (r : ℂ) = 0}.Finite := by
      intro n
      by_contra hinf
      rw [Set.not_finite] at hinf
      obtain ⟨r₀, _, hacc⟩ :=
        hinf.exists_accPt_of_subset_isCompact isCompact_Icc (fun _ hr => hr.1)
      have hr₀_mem : (r₀ : ℂ) ∈ {b : ℂ | |b.im| < 1 / 2} := by simp
      have hfreq : ∃ᶠ z in 𝓝[≠] (r₀ : ℂ), hankelContinuation c' g z = 0 := by
        rw [Filter.frequently_iff]
        intro U hU
        rw [mem_nhdsWithin_iff_exists_mem_nhds_inter] at hU
        obtain ⟨V, hV, hVU⟩ := hU
        obtain ⟨ε, hε_pos, hball⟩ := Metric.mem_nhds_iff.mp hV
        rw [accPt_iff_frequently] at hacc
        obtain ⟨r, ⟨hr_ne, hr_mem⟩, hr_ball⟩ :=
          (hacc.and_eventually (Metric.ball_mem_nhds r₀ hε_pos)).exists
        have hrC_ne : (r : ℂ) ≠ (r₀ : ℂ) := fun he => hr_ne (Complex.ofReal_injective he)
        have hrC_ball : (r : ℂ) ∈ Metric.ball (r₀ : ℂ) ε := by
          rw [Metric.mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real,
            Real.norm_eq_abs]
          simpa [Metric.mem_ball, Real.dist_eq] using hr_ball
        exact ⟨(r : ℂ), hVU ⟨hball hrC_ball, hrC_ne⟩, hr_mem.2⟩
      have hzero := han.eqOn_zero_of_preconnected_of_frequently_eq_zero hpre hr₀_mem hfreq
      have hx_mem : (x : ℂ) ∈ {b : ℂ | |b.im| < 1 / 2} := by simp
      have hx0 := hzero hx_mem
      simp only [Pi.zero_apply] at hx0
      rw [hankelContinuation_ofReal hc0 hg x, Complex.ofReal_eq_zero] at hx0
      exact hx_ne hx0
    exact Set.countable_iUnion fun n => (hfin n).countable
  have hσ_cnt :
      {σ : ℝ | σ ∈ slitPreimage ∧ hankelContinuation c' g (slitBoundaryMap σ : ℂ) = 0}.Countable := by
    have hsub : {σ : ℝ | σ ∈ slitPreimage ∧ hankelContinuation c' g (slitBoundaryMap σ : ℂ) = 0} ⊆
        ⋃ r ∈ {r : ℝ | hankelContinuation c' g (r : ℂ) = 0},
          {σ : ℝ | σ ∈ slitPreimage ∧ slitBoundaryMap σ = r} := fun σ ⟨hσ, h0⟩ =>
      mem_iUnion₂.mpr ⟨slitBoundaryMap σ, h0, hσ, rfl⟩
    exact (hz_re_cnt.biUnion fun r _ => (slitBoundaryMap_preimage_finite r).countable).mono hsub
  have hnull : volume {σ : ℝ | σ ∈ slitPreimage ∧ hankelContinuation c' g (slitBoundaryMap σ : ℂ) = 0} = 0 :=
    hσ_cnt.measure_zero volume
  change ∀ᵐ σ ∂(volume.restrict (Ioo (-1 : ℝ) 0 ∪ Ioi 1)),
      hankelContinuation c' g (slitBoundaryMap σ : ℂ) ≠ 0
  rw [ae_restrict_iff' (measurableSet_Ioo.union measurableSet_Ioi)]
  filter_upwards [compl_mem_ae_iff.mpr hnull] with σ hσ hmem h0
  exact hσ ⟨hmem, h0⟩

/-! ### 2. The slit-mass bound `(eSlitMass)` -/

lemma continuous_besselI0 : Continuous Bessel.besselI0 := by
  have hdiff : ∀ z₀ : ℝ, HasDerivAt Bessel.besselI0
      (π⁻¹ * ∫ θ in (0 : ℝ)..π, Real.cos θ * Real.exp (z₀ * Real.cos θ)) z₀ := by
    intro z₀
    let F : ℝ → ℝ → ℝ := fun z θ => Real.exp (z * Real.cos θ)
    let F' : ℝ → ℝ → ℝ := fun z θ => Real.cos θ * Real.exp (z * Real.cos θ)
    have hF_meas : ∀ᶠ z in 𝓝 z₀, AEStronglyMeasurable (F z) (volume.restrict (Ι 0 π)) :=
      Eventually.of_forall fun z => (by fun_prop : Continuous (F z)).aestronglyMeasurable
    have hF_int : IntervalIntegrable (F z₀) volume 0 π :=
      (by fun_prop : Continuous (F z₀)).intervalIntegrable 0 π
    have hF'_meas : AEStronglyMeasurable (F' z₀) (volume.restrict (Ι 0 π)) :=
      (by fun_prop : Continuous (F' z₀)).aestronglyMeasurable
    have hbound : ∀ᵐ θ ∂volume, θ ∈ Ι (0 : ℝ) π → ∀ z ∈ Metric.ball z₀ 1,
        ‖F' z θ‖ ≤ Real.exp (|z₀| + 1) := by
      refine Eventually.of_forall fun θ _ z hz => ?_
      simp only [F', Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      have h1 : |Real.cos θ| ≤ 1 := Real.abs_cos_le_one θ
      have h2 : z * Real.cos θ ≤ |z₀| + 1 := by
        have hzb : |z - z₀| < 1 := Real.dist_eq z z₀ ▸ Metric.mem_ball.mp hz
        have hza : |z| ≤ |z₀| + 1 := by linarith [abs_sub_abs_le_abs_sub z z₀]
        calc z * Real.cos θ ≤ |z * Real.cos θ| := le_abs_self _
          _ = |z| * |Real.cos θ| := abs_mul _ _
          _ ≤ (|z₀| + 1) * 1 := mul_le_mul hza h1 (abs_nonneg _) (by positivity)
          _ = |z₀| + 1 := mul_one _
      calc |Real.cos θ| * Real.exp (z * Real.cos θ)
          ≤ 1 * Real.exp (|z₀| + 1) := mul_le_mul h1 (Real.exp_le_exp.mpr h2)
            (Real.exp_pos _).le zero_le_one
        _ = Real.exp (|z₀| + 1) := one_mul _
    have hdiff_pt : ∀ᵐ θ ∂volume, θ ∈ Ι (0 : ℝ) π → ∀ z ∈ Metric.ball z₀ 1,
        HasDerivAt (fun w => F w θ) (F' z θ) z := by
      refine Eventually.of_forall fun θ _ z _ => ?_
      dsimp [F, F']
      exact (((hasDerivAt_id z).mul_const (Real.cos θ)).exp).congr_deriv (by simp [mul_comm])
    have hd := (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (Metric.ball_mem_nhds z₀ one_pos) hF_meas hF_int hF'_meas hbound
      intervalIntegrable_const hdiff_pt).2
    have heq : (fun z : ℝ => π⁻¹ * ∫ θ in (0 : ℝ)..π, F z θ) = Bessel.besselI0 := by
      ext z; rw [Bessel.besselI0_integral]; dsimp [F]; ring
    rw [← heq]
    exact hd.const_mul π⁻¹
  exact continuous_iff_continuousAt.mpr fun z => (hdiff z).continuousAt

theorem eSlitMass_pointwise {c' x : ℝ} (hc : 10000 ≤ c') (hx : xiStar ≤ x) :
    besselK (c' / 12) (c' * x ^ 2 / 3) ≤
      6 * Real.sqrt (2 * π) * virasoroProblem.cardyV (c' / 12) (c' * x ^ 2 / 3) := by
  have hc0 : 0 < c' := by linarith
  have hx0 : 0 < x := xiStar_pos.trans_le hx
  have hx_half : xiStar / 2 ≤ x := by linarith [xiStar_pos]
  have hK : besselK (c' / 12) (c' * x ^ 2 / 3) = besselI0 (c' * besselL x) := by
    have := besselK_shift (c' := c') (x := x) (j := 0) hc0 hx0.le
    simpa using this
  have hLz : 0 < c' * besselL x := by unfold besselL; positivity
  have hI0 := besselI0_le_two_mul_exp_div_sqrt hLz
  have hcomp := (besselV_comparison hc hx_half).2
  have ha : (2 : ℝ) ≤ c' / 12 := by linarith
  have hV_eq : virasoroProblem.cardyV (c' / 12) (c' * x ^ 2 / 3) =
      besselV (c' / 12) (c' * x ^ 2 / 3) :=
    virasoro_cardyV_eq_besselV ha (by positivity)
  have hV_pos : 0 < besselV (c' / 12) (c' * x ^ 2 / 3) := by
    rw [← hV_eq]
    have hge := virasoro_cardyV_ge ha (by positivity : 0 ≤ c' * x ^ 2 / 3)
    have ht_pos : 0 < 8 * π ^ 4 * (c' * x ^ 2 / 3) ^ 2 := by positivity
    exact ht_pos.trans_le hge
  have hsq_t : 0 < Real.sqrt (c' * x ^ 2 / 3) := Real.sqrt_pos.mpr (by positivity)
  have hsq_L : 0 < Real.sqrt (c' * besselL x) := Real.sqrt_pos.mpr hLz
  have hsq_x : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hsq_2pi : 0 < Real.sqrt (2 * π) := Real.sqrt_pos.mpr (by positivity)
  have hratio : Real.sqrt (c' * x ^ 2 / 3) / Real.sqrt (c' * besselL x) =
      Real.sqrt x / Real.sqrt (2 * π) := by
    rw [← Real.sqrt_div (by positivity), ← Real.sqrt_div hx0.le]
    congr 1
    unfold besselL
    field_simp [hc0.ne', Real.pi_pos.ne']
  have h1 : Real.exp (c' * besselL x) ≤
      6 * π / Real.sqrt x * Real.sqrt (c' * x ^ 2 / 3) * besselV (c' / 12) (c' * x ^ 2 / 3) := by
    rw [div_le_iff₀ hV_pos] at hcomp
    calc Real.exp (c' * besselL x)
        = Real.sqrt (c' * x ^ 2 / 3) * (1 / Real.sqrt (c' * x ^ 2 / 3) * Real.exp (c' * besselL x)) := by
          field_simp [hsq_t.ne']
      _ ≤ Real.sqrt (c' * x ^ 2 / 3) * (6 * π / Real.sqrt x * besselV (c' / 12) (c' * x ^ 2 / 3)) :=
          mul_le_mul_of_nonneg_left hcomp hsq_t.le
      _ = _ := by ring
  calc besselK (c' / 12) (c' * x ^ 2 / 3)
      = besselI0 (c' * besselL x) := hK
    _ ≤ 2 * Real.exp (c' * besselL x) / Real.sqrt (c' * besselL x) := hI0
    _ ≤ 2 * (6 * π / Real.sqrt x * Real.sqrt (c' * x ^ 2 / 3) *
          besselV (c' / 12) (c' * x ^ 2 / 3)) / Real.sqrt (c' * besselL x) := by
        gcongr
    _ = 12 * π / Real.sqrt x * (Real.sqrt (c' * x ^ 2 / 3) / Real.sqrt (c' * besselL x)) *
          besselV (c' / 12) (c' * x ^ 2 / 3) := by ring
    _ = 12 * π / Real.sqrt x * (Real.sqrt x / Real.sqrt (2 * π)) *
          besselV (c' / 12) (c' * x ^ 2 / 3) := by rw [hratio]
    _ = 6 * Real.sqrt (2 * π) * besselV (c' / 12) (c' * x ^ 2 / 3) := by
        have hsq2 : Real.sqrt (2 * π) * Real.sqrt (2 * π) = 2 * π :=
          Real.mul_self_sqrt (by positivity)
        have heq1 : 12 * π / Real.sqrt x * (Real.sqrt x / Real.sqrt (2 * π)) =
            6 * Real.sqrt (2 * π) := by
          field_simp [hsq_x.ne', hsq_2pi.ne']
          rw [show 12 * π = 6 * (2 * π) by ring, ← hsq2]; ring
        rw [heq1]
    _ = 6 * Real.sqrt (2 * π) * virasoroProblem.cardyV (c' / 12) (c' * x ^ 2 / 3) := by
        rw [hV_eq]

theorem eSlitMass {c' : ℝ} (hc : 10000 ≤ c') {g : ℝ → ℝ}
    (hg : TestClass virasoroProblem (c' / 12) g) :
    IntegrableOn (fun x : ℝ => |g (c' * x ^ 2 / 3)| * besselK (c' / 12) (c' * x ^ 2 / 3))
        (Ioi xiStar) ∧
      ∫ x in Ioi xiStar, |g (c' * x ^ 2 / 3)| * besselK (c' / 12) (c' * x ^ 2 / 3) ≤
        (9 * Real.sqrt (2 * π) / xiStar) * c'⁻¹ * virasoroProblem.cardyNorm (c' / 12) g := by
  have hc0 : 0 < c' := by linarith
  have ha : (2 : ℝ) ≤ c' / 12 := by linarith
  let φ : ℝ → ℝ := fun x => c' * x ^ 2 / 3
  let φ' : ℝ → ℝ := fun x => (2 * c' / 3) * x
  have hφ_xi_pos : 0 < φ xiStar := by dsimp [φ]; positivity [xiStar_pos]
  have hφ_deriv : ∀ x ∈ Ioi xiStar, HasDerivWithinAt φ (φ' x) (Ioi xiStar) x := fun x _ => by
    dsimp [φ, φ']
    have hsq : HasDerivAt (fun s : ℝ => s ^ 2) (2 * x) x := by simpa using hasDerivAt_pow 2 x
    exact ((hsq.const_mul c').div_const 3).congr_deriv (by ring) |>.hasDerivWithinAt
  have hφ_inj : InjOn φ (Ioi xiStar) := fun x hx y hy hxy => by
    dsimp [φ] at hxy
    have hsq : x ^ 2 = y ^ 2 := by
      have hne : c' / 3 ≠ 0 := by positivity
      calc x ^ 2 = (c' * x ^ 2 / 3) / (c' / 3) := by field_simp
        _ = (c' * y ^ 2 / 3) / (c' / 3) := by rw [hxy]
        _ = y ^ 2 := by field_simp
    have hx0 : 0 ≤ x := (xiStar_pos.trans hx).le
    have hy0 : 0 ≤ y := (xiStar_pos.trans hy).le
    nlinarith [sq_nonneg (x - y)]
  have hφ_img : φ '' Ioi xiStar = Ioi (φ xiStar) := by
    ext t
    refine ⟨?_, ?_⟩
    · rintro ⟨x, hx, rfl⟩
      have hlt : xiStar < x := hx
      have hxs : 0 < xiStar := xiStar_pos
      have hsq : xiStar ^ 2 < x ^ 2 := by nlinarith
      dsimp [φ]; exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_left hsq hc0) (by norm_num)
    · intro ht
      have ht_pos : 0 < t := lt_trans hφ_xi_pos ht
      have h3t_pos : 0 ≤ 3 * t / c' := div_nonneg (by positivity) hc0.le
      refine ⟨Real.sqrt (3 * t / c'), ?_, ?_⟩
      · have hlt : xiStar ^ 2 < 3 * t / c' := by
          rw [lt_div_iff₀ hc0]
          have hgt : φ xiStar < t := ht
          dsimp [φ] at hgt; linarith
        rw [← Real.sqrt_sq xiStar_pos.le]
        exact Real.sqrt_lt_sqrt (sq_nonneg _) hlt
      · dsimp [φ]
        rw [Real.sq_sqrt h3t_pos]
        field_simp [hc0.ne']
  let fV : ℝ → ℝ := fun t => |g t| * virasoroProblem.cardyV (c' / 12) t
  have hfV_int : IntegrableOn fV (Ioi (φ xiStar)) :=
    hg.int_cardy.mono_set (Ioi_subset_Ioi hφ_xi_pos.le)
  have hfV_pull : IntegrableOn (fun x : ℝ => |φ' x| • fV (φ x)) (Ioi xiStar) :=
    (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hφ_deriv hφ_inj fV).mp
      (hφ_img ▸ hfV_int)
  have hfV_eq_int : ∫ x in Ioi xiStar, |φ' x| • fV (φ x) = ∫ t in Ioi (φ xiStar), fV t := by
    rw [← hφ_img]
    exact (integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hφ_deriv hφ_inj fV).symm
  have hM_ge : ∫ t in Ioi (φ xiStar), fV t ≤ virasoroProblem.cardyNorm (c' / 12) g := by
    unfold FixedWeightProblem.cardyNorm
    refine setIntegral_mono_set hg.int_cardy ?_
      (ae_of_all _ fun t ht => Ioi_subset_Ioi hφ_xi_pos.le ht)
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => mul_nonneg (abs_nonneg _)
      (virasoroProblem.cardyV_nonneg (by rw [virasoroProblem_totalShift]; linarith) ht.le)
  have hK_eq_I0 : ∀ x ∈ Ioi xiStar,
      besselK (c' / 12) (φ x) = besselI0 (c' * besselL x) := fun x hx => by
    have := besselK_shift (c' := c') (x := x) (j := 0) hc0 (xiStar_pos.trans hx).le
    simpa [φ] using this
  have hmeas_K : AEStronglyMeasurable
      (fun x : ℝ => |g (φ x)| * besselK (c' / 12) (φ x)) (volume.restrict (Ioi xiStar)) := by
    have hcont_g : ContinuousOn (fun x : ℝ => |g (φ x)|) (Ioi xiStar) :=
      (hg.cont.abs).comp (by fun_prop : Continuous φ).continuousOn
        (fun x _ => show 0 ≤ c' * x ^ 2 / 3 by positivity)
    have hcont_L : Continuous besselL := by unfold besselL; fun_prop
    have hcont_I0 : Continuous fun x : ℝ => besselI0 (c' * besselL x) :=
      continuous_besselI0.comp (continuous_const.mul hcont_L)
    have hcont_prod : ContinuousOn (fun x : ℝ => |g (φ x)| * besselI0 (c' * besselL x)) (Ioi xiStar) :=
      hcont_g.mul hcont_I0.continuousOn
    refine (hcont_prod.aestronglyMeasurable measurableSet_Ioi).congr ?_
    exact ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => by simp only [hK_eq_I0 x hx]
  let C_slit : ℝ := 9 * Real.sqrt (2 * π) / xiStar
  have hCslit_nn : 0 ≤ C_slit := div_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) xiStar_pos.le
  have hdom : ∀ x ∈ Ioi xiStar,
      |g (φ x)| * besselK (c' / 12) (φ x) ≤ C_slit * c'⁻¹ * (|φ' x| • fV (φ x)) := by
    intro x hx
    have hx_ge : xiStar ≤ x := hx.le
    have hK_le := eSlitMass_pointwise hc hx_ge
    have hV_nn : 0 ≤ virasoroProblem.cardyV (c' / 12) (φ x) :=
      virasoroProblem.cardyV_nonneg (by rw [virasoroProblem_totalShift]; linarith)
        (by dsimp [φ]; positivity)
    have hφ'_pos : 0 < φ' x := by dsimp [φ']; positivity [xiStar_pos.trans hx]
    have hφ'_abs : |φ' x| = (2 * c' / 3) * x := abs_of_pos hφ'_pos
    have hxi : (2 * c' / 3) * xiStar ≤ |φ' x| := by rw [hφ'_abs]; gcongr
    have hratio : C_slit * c'⁻¹ * |φ' x| ≥ 6 * Real.sqrt (2 * π) := by
      dsimp [C_slit]
      calc 6 * Real.sqrt (2 * π)
          = (9 * Real.sqrt (2 * π) / xiStar) * c'⁻¹ * ((2 * c' / 3) * xiStar) := by
            field_simp [xiStar_pos.ne', hc0.ne']; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hxi (mul_nonneg hCslit_nn (inv_nonneg.mpr hc0.le))
    have hprod_nn : 0 ≤ |g (φ x)| * virasoroProblem.cardyV (c' / 12) (φ x) :=
      mul_nonneg (abs_nonneg _) hV_nn
    calc |g (φ x)| * besselK (c' / 12) (φ x)
        ≤ |g (φ x)| * (6 * Real.sqrt (2 * π) * virasoroProblem.cardyV (c' / 12) (φ x)) := by gcongr
      _ = 6 * Real.sqrt (2 * π) * fV (φ x) := by dsimp [fV]; ring
      _ ≤ (C_slit * c'⁻¹ * |φ' x|) * fV (φ x) := mul_le_mul_of_nonneg_right hratio hprod_nn
      _ = C_slit * c'⁻¹ * (|φ' x| • fV (φ x)) := by simp [smul_eq_mul, mul_assoc]
  have hint_K : IntegrableOn (fun x : ℝ => |g (φ x)| * besselK (c' / 12) (φ x)) (Ioi xiStar) := by
    refine (hfV_pull.const_mul (C_slit * c'⁻¹)).mono' hmeas_K ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun x hx => ?_
    rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) besselK_nonneg)]
    exact hdom x hx
  refine ⟨hint_K, ?_⟩
  calc ∫ x in Ioi xiStar, |g (φ x)| * besselK (c' / 12) (φ x)
      ≤ ∫ x in Ioi xiStar, C_slit * c'⁻¹ * (|φ' x| • fV (φ x)) :=
        setIntegral_mono_on hint_K (hfV_pull.const_mul _) measurableSet_Ioi hdom
    _ = C_slit * c'⁻¹ * ∫ x in Ioi xiStar, |φ' x| • fV (φ x) := by rw [integral_const_mul]
    _ = C_slit * c'⁻¹ * ∫ t in Ioi (φ xiStar), fV t := by rw [hfV_eq_int]
    _ ≤ C_slit * c'⁻¹ * virasoroProblem.cardyNorm (c' / 12) g := by
        exact mul_le_mul_of_nonneg_left hM_ge (mul_nonneg hCslit_nn (inv_nonneg.mpr hc0.le))

/-! ### 3. Slit pullback identities and `log slitDensity` integrability -/

lemma sigmaStar_mem_Ioo : sigmaStar ∈ Ioo (-1 : ℝ) 0 :=
  ⟨by linarith [sigmaStar_gt_neg_half], sigmaStar_neg⟩

lemma sigmaPlus_mem_Ioi : sigmaPlus ∈ Ioi (1 : ℝ) := by
  change 1 < sigmaPlus; linarith [sigmaPlus_gt_two]

lemma invJacobian_nonneg' (σ : ℝ) : 0 ≤ invJacobian σ := by
  unfold invJacobian; positivity

lemma rightSlitDensity_nonneg' (x : ℝ) {y : ℝ} (hy : 0 ≤ y) (σ : ℝ) :
    0 ≤ rightSlitDensity x y σ := by
  unfold rightSlitDensity
  exact add_nonneg (mul_nonneg (poissonKernel_nonneg hy _) (invJacobian_nonneg' _))
    (mul_nonneg (poissonKernel_nonneg hy _) (invJacobian_nonneg' _))

lemma leftSlitDensity_nonneg' (x : ℝ) {y : ℝ} (hy : 0 ≤ y) (σ : ℝ) :
    0 ≤ leftSlitDensity x y σ := by
  unfold leftSlitDensity
  exact add_nonneg (mul_nonneg (poissonKernel_nonneg hy _) (invJacobian_nonneg' _))
    (mul_nonneg (poissonKernel_nonneg hy _) (invJacobian_nonneg' _))

lemma hasDerivAt_slitInv {σ : ℝ} (hσ : σ ≠ 1) :
    HasDerivAt slitInv (-2 / (σ - 1) ^ 2) σ := by
  unfold slitInv
  have h1 : HasDerivAt (fun τ : ℝ => 1 + τ) 1 σ := by simpa using (hasDerivAt_id σ).const_add (1 : ℝ)
  have h2 : HasDerivAt (fun τ : ℝ => τ - 1) 1 σ := by simpa using (hasDerivAt_id σ).sub_const (1 : ℝ)
  have hd := h1.div h2 (sub_ne_zero.mpr hσ)
  refine hd.congr_deriv ?_
  have hne : σ - 1 ≠ 0 := sub_ne_zero.mpr hσ
  field_simp [hne]; ring

lemma hasDerivAt_leftSlitInv {σ : ℝ} (hσ : σ ≠ 1) :
    HasDerivAt leftSlitInv (-2 / (σ - 1) ^ 2) σ := by
  unfold leftSlitInv
  have h1 : HasDerivAt (fun τ : ℝ => τ + 1) 1 σ := by simpa using (hasDerivAt_id σ).add_const (1 : ℝ)
  have h2 : HasDerivAt (fun τ : ℝ => τ - 1) 1 σ := by simpa using (hasDerivAt_id σ).sub_const (1 : ℝ)
  have hd := h1.div h2 (sub_ne_zero.mpr hσ)
  refine hd.congr_deriv ?_
  have hne : σ - 1 ≠ 0 := sub_ne_zero.mpr hσ
  field_simp [hne]; ring

lemma slitBoundaryMap_leftSlitInv {σ : ℝ} (hσ : 1 < σ) :
    slitBoundaryMap (leftSlitInv σ) = slitBoundaryMap σ := by
  rw [slitBoundaryMap_eq_leftBranch, slitBoundaryMap_eq_leftBranch]
  unfold leftSlitInv
  have h1 : σ - 1 ≠ 0 := sub_ne_zero.mpr hσ.ne'
  have h2 : σ ≠ 0 := by linarith
  have h3 : σ + 1 ≠ 0 := by linarith
  have ha : (σ + 1) / (σ - 1) - 1 = 2 / (σ - 1) := by rw [div_sub_one h1]; ring_nf
  have hb : (σ + 1) / (σ - 1) + 1 = 2 * σ / (σ - 1) := by rw [div_add_one h1]; ring_nf
  rw [ha, hb]
  congr 2
  field_simp [h1, h2, h3]

lemma hasDerivAt_slitBoundaryMap_Ioi {σ : ℝ} (hσ : σ ∈ Ioi (1 : ℝ) \ {sigmaPlus}) :
    HasDerivAt slitBoundaryMap
      (-(σ - sigmaStar) * (σ - sigmaPlus) / (2 * π * σ * (σ ^ 2 - 1))) σ := by
  have hgt : 1 < σ := hσ.1
  have hm1 : 0 < σ - 1 := sub_pos.mpr hgt
  have h0 : 0 < σ := by linarith
  have hp1 : 0 < σ + 1 := by linarith
  let f : ℝ → ℝ := fun τ => (2 * π)⁻¹ * (Real.log (τ - 1) - Real.log τ - Real.log (τ + 1))
  have hev : slitBoundaryMap =ᶠ[𝓝 σ] f := by
    filter_upwards [isOpen_Ioi.mem_nhds hgt] with τ hτ
    have ha : 0 < τ - 1 := sub_pos.mpr hτ
    have hb : 0 < τ := by linarith
    have hc : 0 < τ + 1 := by linarith
    rw [slitBoundaryMap_eq_leftBranch]
    dsimp [f]
    rw [Real.log_div ha.ne' (mul_pos hb hc).ne', Real.log_mul hb.ne' hc.ne']
    ring
  have hd1 : HasDerivAt (fun τ => Real.log (τ - 1)) (1 / (σ - 1)) σ :=
    (((hasDerivAt_id' σ).sub_const 1).log hm1.ne').congr_deriv (by rw [one_div])
  have hd2 : HasDerivAt (fun τ => Real.log τ) (1 / σ) σ := by
    simpa [one_div] using Real.hasDerivAt_log h0.ne'
  have hd3 : HasDerivAt (fun τ => Real.log (τ + 1)) (1 / (σ + 1)) σ :=
    (((hasDerivAt_id' σ).add_const 1).log hp1.ne').congr_deriv (by rw [one_div])
  have hdf : HasDerivAt f ((2 * π)⁻¹ * (1 / (σ - 1) - 1 / σ - 1 / (σ + 1))) σ :=
    ((hd1.sub hd2).sub hd3).const_mul (2 * π)⁻¹
  refine (hdf.congr_of_eventuallyEq hev).congr_deriv ?_
  have hpi : π ≠ 0 := Real.pi_pos.ne'
  have hs2 : σ ^ 2 - 1 ≠ 0 := by nlinarith
  have hsq : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  unfold sigmaStar sigmaPlus
  field_simp [hm1.ne', h0.ne', hp1.ne', hpi, hs2]
  ring_nf; rw [hsq]; ring

lemma invJacobian_eq_inv_abs_deriv {σ : ℝ} :
    invJacobian σ = |-(σ - sigmaStar) * (σ - sigmaPlus) / (2 * π * σ * (σ ^ 2 - 1))|⁻¹ := by
  unfold invJacobian
  rw [abs_div, inv_div, abs_mul]
  have h1 : |2 * π * σ * (σ ^ 2 - 1)| = 2 * π * (|σ| * |σ ^ 2 - 1|) := by
    rw [show 2 * π * σ * (σ ^ 2 - 1) = (2 * π) * (σ * (σ ^ 2 - 1)) by ring,
      abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π), abs_mul]
  rw [h1, abs_mul, abs_neg]

lemma invJacobian_slitInv {σ : ℝ} (hσ : σ ∈ Ioo (-1 : ℝ) 0) :
    invJacobian (slitInv σ) = (2 / (σ - 1) ^ 2) * invJacobian σ := by
  by_cases hs : σ = sigmaStar
  · subst hs; rw [slitInv_sigmaStar]; unfold invJacobian; simp
  · have hσ_mem : σ ∈ Ioo (-1 : ℝ) 0 \ {sigmaStar} := ⟨hσ, hs⟩
    have hslit_Ioo : slitInv σ ∈ Ioo (-1 : ℝ) 0 := slitInv_mem_Ioo hσ
    have hslit_ne : slitInv σ ≠ sigmaStar := by
      rw [← sub_ne_zero, slitInv_sub_sigmaStar_eq (by linarith [hσ.2])]
      exact div_ne_zero (mul_ne_zero (neg_ne_zero.mpr (by positivity)) (sub_ne_zero.mpr hs))
        (by linarith [hσ.2])
    have hev : slitBoundaryMap =ᶠ[𝓝 σ] (fun τ => slitBoundaryMap (slitInv τ)) := by
      filter_upwards [isOpen_Ioo.mem_nhds hσ] with τ hτ
      exact (slitBoundaryMap_slitInv hτ).symm
    have hd_comp : HasDerivAt (fun τ => slitBoundaryMap (slitInv τ))
        ((-(slitInv σ - sigmaStar) * (slitInv σ - sigmaPlus) /
          (2 * π * slitInv σ * (slitInv σ ^ 2 - 1))) * (-2 / (σ - 1) ^ 2)) σ :=
      (hasDerivAt_slitBoundaryMap ⟨hslit_Ioo, hslit_ne⟩).comp σ
        (hasDerivAt_slitInv (by linarith [hσ.2]))
    have hd_eq := (hd_comp.congr_of_eventuallyEq hev).unique (hasDerivAt_slitBoundaryMap hσ_mem)
    have hB'_ne : -(slitInv σ - sigmaStar) * (slitInv σ - sigmaPlus) /
        (2 * π * slitInv σ * (slitInv σ ^ 2 - 1)) ≠ 0 := by
      have h2 := hslit_Ioo.2
      have hm1 := hslit_Ioo.1
      have hplus : slitInv σ - sigmaPlus ≠ 0 := by linarith [sigmaPlus_gt_two]
      have hsq : slitInv σ ^ 2 - 1 ≠ 0 := by nlinarith
      exact div_ne_zero (mul_ne_zero (neg_ne_zero.mpr (sub_ne_zero.mpr hslit_ne)) hplus)
        (mul_ne_zero (mul_ne_zero (by positivity) h2.ne) hsq)
    have habs : |-(slitInv σ - sigmaStar) * (slitInv σ - sigmaPlus) /
          (2 * π * slitInv σ * (slitInv σ ^ 2 - 1))| * (2 / (σ - 1) ^ 2) =
        |-(σ - sigmaStar) * (σ - sigmaPlus) / (2 * π * σ * (σ ^ 2 - 1))| := by
      have h1 : |-2 / (σ - 1) ^ 2| = 2 / (σ - 1) ^ 2 := by
        rw [abs_div, abs_neg, abs_of_pos (by norm_num), abs_of_pos (sq_pos_of_ne_zero (by linarith [hσ.2]))]
      rw [← h1, ← abs_mul, hd_eq]
    rw [invJacobian_eq_inv_abs_deriv, invJacobian_eq_inv_abs_deriv, ← habs, mul_inv]
    have hs1 : σ - 1 ≠ 0 := by linarith [hσ.2]
    have h2pos : 2 / (σ - 1) ^ 2 ≠ 0 := div_ne_zero (by norm_num) (pow_ne_zero 2 hs1)
    field_simp [hB'_ne, h2pos, hs1]

lemma invJacobian_leftSlitInv {σ : ℝ} (hσ : 1 < σ) :
    invJacobian (leftSlitInv σ) = (2 / (σ - 1) ^ 2) * invJacobian σ := by
  by_cases hp : σ = sigmaPlus
  · subst hp; rw [leftSlitInv_sigmaPlus]; unfold invJacobian; simp
  · have hσ_mem : σ ∈ Ioi (1 : ℝ) \ {sigmaPlus} := ⟨hσ, hp⟩
    have hl_gt : 1 < leftSlitInv σ := leftSlitInv_gt_one hσ
    have hl_ne : leftSlitInv σ ≠ sigmaPlus := by
      rw [← sub_ne_zero, leftSlitInv_sub_sigmaPlus_eq hσ.ne']
      exact div_ne_zero (mul_ne_zero (neg_ne_zero.mpr (by positivity)) (sub_ne_zero.mpr hp))
        (sub_ne_zero.mpr hσ.ne')
    have hev : slitBoundaryMap =ᶠ[𝓝 σ] (fun τ => slitBoundaryMap (leftSlitInv τ)) := by
      filter_upwards [isOpen_Ioi.mem_nhds hσ] with τ hτ
      exact (slitBoundaryMap_leftSlitInv hτ).symm
    have hd_comp : HasDerivAt (fun τ => slitBoundaryMap (leftSlitInv τ))
        ((-(leftSlitInv σ - sigmaStar) * (leftSlitInv σ - sigmaPlus) /
          (2 * π * leftSlitInv σ * (leftSlitInv σ ^ 2 - 1))) * (-2 / (σ - 1) ^ 2)) σ :=
      (hasDerivAt_slitBoundaryMap_Ioi ⟨hl_gt, hl_ne⟩).comp σ (hasDerivAt_leftSlitInv hσ.ne')
    have hd_eq := (hd_comp.congr_of_eventuallyEq hev).unique (hasDerivAt_slitBoundaryMap_Ioi hσ_mem)
    have hB'_ne : -(leftSlitInv σ - sigmaStar) * (leftSlitInv σ - sigmaPlus) /
        (2 * π * leftSlitInv σ * (leftSlitInv σ ^ 2 - 1)) ≠ 0 := by
      have hstar : leftSlitInv σ - sigmaStar ≠ 0 := by linarith [sigmaStar_neg]
      have hsq : leftSlitInv σ ^ 2 - 1 ≠ 0 := by nlinarith
      exact div_ne_zero (mul_ne_zero (neg_ne_zero.mpr hstar) (sub_ne_zero.mpr hl_ne))
        (mul_ne_zero (mul_ne_zero (by positivity) (by linarith)) hsq)
    have habs : |-(leftSlitInv σ - sigmaStar) * (leftSlitInv σ - sigmaPlus) /
          (2 * π * leftSlitInv σ * (leftSlitInv σ ^ 2 - 1))| * (2 / (σ - 1) ^ 2) =
        |-(σ - sigmaStar) * (σ - sigmaPlus) / (2 * π * σ * (σ ^ 2 - 1))| := by
      have h1 : |-2 / (σ - 1) ^ 2| = 2 / (σ - 1) ^ 2 := by
        rw [abs_div, abs_neg, abs_of_pos (by norm_num), abs_of_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr hσ.ne'))]
      rw [← h1, ← abs_mul, hd_eq]
    rw [invJacobian_eq_inv_abs_deriv, invJacobian_eq_inv_abs_deriv, ← habs, mul_inv]
    have hs1 : σ - 1 ≠ 0 := sub_ne_zero.mpr hσ.ne'
    have h2pos : 2 / (σ - 1) ^ 2 ≠ 0 := div_ne_zero (by norm_num) (pow_ne_zero 2 hs1)
    field_simp [hB'_ne, h2pos, hs1]

lemma leftSlitInv_leftSlitInv {σ : ℝ} (hσ : σ ≠ 1) : leftSlitInv (leftSlitInv σ) = σ := by
  unfold leftSlitInv
  have h1 : σ - 1 ≠ 0 := sub_ne_zero.mpr hσ
  have h2 : (σ + 1) / (σ - 1) - 1 ≠ 0 := by
    rw [div_sub_one h1]; exact div_ne_zero (by norm_num) h1
  field_simp; ring

lemma rightSlitDensity_slitInv {x y σ : ℝ} (hσ : σ ≠ 1) :
    rightSlitDensity x y (slitInv σ) = rightSlitDensity x y σ := by
  unfold rightSlitDensity
  rw [slitInv_slitInv hσ, add_comm]

lemma leftSlitDensity_leftSlitInv {x y σ : ℝ} (hσ : σ ≠ 1) :
    leftSlitDensity x y (leftSlitInv σ) = leftSlitDensity x y σ := by
  unfold leftSlitDensity
  rw [leftSlitInv_leftSlitInv hσ, add_comm]

lemma invJacobian_pos_left {σ : ℝ} (hσ : σ ∈ Ioo (-1 : ℝ) 0 \ {sigmaStar}) : 0 < invJacobian σ := by
  unfold invJacobian
  have h1 : σ ≠ 0 := hσ.1.2.ne
  have h2 : σ ^ 2 - 1 ≠ 0 := by nlinarith [hσ.1.1, hσ.1.2]
  have h3 : σ - sigmaStar ≠ 0 := sub_ne_zero.mpr hσ.2
  have h4 : σ - sigmaPlus ≠ 0 := by linarith [hσ.1.2, sigmaPlus_gt_two]
  positivity

lemma invJacobian_pos_right {σ : ℝ} (hσ : σ ∈ Ioi (1 : ℝ) \ {sigmaPlus}) : 0 < invJacobian σ := by
  unfold invJacobian
  have hgt : 1 < σ := hσ.1
  have h1 : σ ≠ 0 := by linarith
  have h2 : σ ^ 2 - 1 ≠ 0 := by nlinarith
  have h3 : σ - sigmaStar ≠ 0 := by linarith [sigmaStar_neg]
  have h4 : σ - sigmaPlus ≠ 0 := sub_ne_zero.mpr hσ.2
  positivity

lemma poissonKernel_pos {x y : ℝ} (hy : 0 < y) (σ : ℝ) : 0 < poissonKernel x y σ := by
  unfold poissonKernel
  positivity

lemma rightSlitDensity_pos {x y σ : ℝ} (hy : 0 < y) (hσ : σ ∈ Ioo (-1 : ℝ) 0 \ {sigmaStar}) :
    0 < rightSlitDensity x y σ := by
  unfold rightSlitDensity
  have h1 := mul_pos (poissonKernel_pos (x := x) hy σ) (invJacobian_pos_left hσ)
  have h2 := mul_nonneg (poissonKernel_nonneg (x := x) hy.le (slitInv σ))
    (invJacobian_nonneg' (slitInv σ))
  linarith

lemma leftSlitDensity_pos {x y σ : ℝ} (hy : 0 < y) (hσ : σ ∈ Ioi (1 : ℝ) \ {sigmaPlus}) :
    0 < leftSlitDensity x y σ := by
  unfold leftSlitDensity
  have h1 := mul_pos (poissonKernel_pos (x := x) hy σ) (invJacobian_pos_right hσ)
  have h2 := mul_nonneg (poissonKernel_nonneg (x := x) hy.le (leftSlitInv σ))
    (invJacobian_nonneg' (leftSlitInv σ))
  linarith

lemma slitInv_image_Ioo_left : slitInv '' Ioo (-1 : ℝ) sigmaStar = Ioo sigmaStar 0 := by
  have hrt : 0 < √2 := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)
  ext τ
  refine ⟨?_, ?_⟩
  · rintro ⟨σ, hσ, rfl⟩
    have hIoo := slitInv_mem_Ioo ⟨hσ.1, hσ.2.trans sigmaStar_neg⟩
    refine ⟨?_, hIoo.2⟩
    have heq := slitInv_sub_sigmaStar_eq (show σ ≠ 1 by linarith [hσ.2, sigmaStar_neg])
    have hpos : 0 < slitInv σ - sigmaStar := by
      rw [heq]
      exact div_pos (mul_pos_of_neg_of_neg (neg_neg_of_pos hrt) (sub_neg.mpr hσ.2)) (by linarith [hσ.2, sigmaStar_neg])
    linarith
  · intro hτ
    have hIoo : τ ∈ Ioo (-1 : ℝ) 0 := ⟨by linarith [sigmaStar_gt_neg_half, hτ.1], hτ.2⟩
    refine ⟨slitInv τ, ⟨(slitInv_mem_Ioo hIoo).1, ?_⟩, slitInv_slitInv (by linarith [hτ.2])⟩
    have heq := slitInv_sub_sigmaStar_eq (show τ ≠ 1 by linarith [hτ.2])
    have hneg : slitInv τ - sigmaStar < 0 := by
      rw [heq]
      exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_neg_of_pos hrt) (sub_pos.mpr hτ.1))
        (by linarith [hτ.2])
    change slitInv τ < sigmaStar
    linarith

lemma injOn_slitInv_Ioo : InjOn slitInv (Ioo (-1 : ℝ) sigmaStar) := fun x hx y hy h => by
  have hx1 : x ≠ 1 := by linarith [hx.2, sigmaStar_neg]
  have hy1 : y ≠ 1 := by linarith [hy.2, sigmaStar_neg]
  calc x = slitInv (slitInv x) := (slitInv_slitInv hx1).symm
    _ = slitInv (slitInv y) := by rw [h]
    _ = y := slitInv_slitInv hy1

lemma leftSlitInv_image_Ioi_right : leftSlitInv '' Ioi sigmaPlus = Ioo (1 : ℝ) sigmaPlus := by
  have hrt : 0 < √2 := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)
  ext τ
  refine ⟨?_, ?_⟩
  · rintro ⟨σ, hσ, rfl⟩
    have hgt1 : 1 < σ := by linarith [sigmaPlus_gt_two, show sigmaPlus < σ from hσ]
    refine ⟨leftSlitInv_gt_one hgt1, ?_⟩
    have heq := leftSlitInv_sub_sigmaPlus_eq hgt1.ne'
    have hneg : leftSlitInv σ - sigmaPlus < 0 := by
      rw [heq]
      exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_neg_of_pos hrt)
        (sub_pos.mpr (show sigmaPlus < σ from hσ))) (sub_pos.mpr hgt1)
    linarith
  · intro hτ
    have hgt1 : 1 < τ := hτ.1
    refine ⟨leftSlitInv τ, ?_, leftSlitInv_leftSlitInv hgt1.ne'⟩
    have heq := leftSlitInv_sub_sigmaPlus_eq hgt1.ne'
    have hpos : 0 < leftSlitInv τ - sigmaPlus := by
      rw [heq]
      exact div_pos (mul_pos_of_neg_of_neg (neg_neg_of_pos hrt) (sub_neg.mpr hτ.2)) (sub_pos.mpr hgt1)
    change sigmaPlus < leftSlitInv τ
    linarith

lemma injOn_leftSlitInv_Ioi : InjOn leftSlitInv (Ioi sigmaPlus) := fun x hx y hy h => by
  have hx1 : x ≠ 1 := by linarith [sigmaPlus_gt_two, show sigmaPlus < x from hx]
  have hy1 : y ≠ 1 := by linarith [sigmaPlus_gt_two, show sigmaPlus < y from hy]
  calc x = leftSlitInv (leftSlitInv x) := (leftSlitInv_leftSlitInv hx1).symm
    _ = leftSlitInv (leftSlitInv y) := by rw [h]
    _ = y := leftSlitInv_leftSlitInv hy1

lemma continuousOn_slitBoundaryMap_slitPreimage' : ContinuousOn slitBoundaryMap slitPreimage := by
  unfold slitBoundaryMap
  refine continuousOn_const.mul (ContinuousOn.log ?_ ?_)
  · refine (continuousOn_const.sub continuousOn_id).div
      (continuousOn_id.neg.mul (continuousOn_const.add continuousOn_id)) fun σ hσ => ?_
    rcases hσ with ⟨hm1, h0⟩ | h1
    · exact mul_ne_zero (by linarith) (by linarith)
    · have hgt : 1 < σ := h1; exact mul_ne_zero (by linarith) (by linarith)
  · intro σ hσ; exact (slitBoundaryMap_pos_quotient hσ).ne'

lemma slitBoundaryMap_strictAntiOn_left :
    StrictAntiOn slitBoundaryMap (Ioc (-1 : ℝ) sigmaStar ∩ Ioo (-1) 0) := by
  refine strictAntiOn_of_deriv_neg ((convex_Ioc (-1) sigmaStar).inter (convex_Ioo (-1) 0)) ?_ ?_
  · exact continuousOn_slitBoundaryMap_slitPreimage'.mono
      (Set.inter_subset_right.trans Set.subset_union_left)
  · intro σ hσ
    have hmem_s := interior_subset hσ
    have hlt : σ < sigmaStar := lt_of_le_of_ne hmem_s.1.2 (fun h => by
      subst h
      obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hσ)
      have hmem := @hsub (sigmaStar + ε / 2) (Metric.mem_ball.mpr (by
        rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos (half_pos hε)]; linarith))
      linarith [hmem.1.2, hε])
    have hd := hasDerivAt_slitBoundaryMap ⟨hmem_s.2, hlt.ne⟩
    rw [hd.deriv]
    have hnum : -(σ - sigmaStar) * (σ - sigmaPlus) < 0 :=
      mul_neg_of_pos_of_neg (by linarith) (by linarith [hmem_s.2.2, sigmaPlus_gt_two])
    have hden : 0 < 2 * π * σ * (σ ^ 2 - 1) := by
      have hsq : σ ^ 2 - 1 < 0 := by nlinarith [hmem_s.2.1, hmem_s.2.2]
      have h2pis : 2 * π * σ < 0 := mul_neg_of_pos_of_neg (by positivity) hmem_s.2.2
      exact mul_pos_of_neg_of_neg h2pis hsq
    exact div_neg_of_neg_of_pos hnum hden

lemma slitBoundaryMap_image_Ioo_left :
    slitBoundaryMap '' Ioo (-1 : ℝ) sigmaStar = Ioi xiStar := by
  have hsub : Ioo (-1 : ℝ) sigmaStar ⊆ Ioc (-1 : ℝ) sigmaStar ∩ Ioo (-1) 0 := fun σ hσ =>
    ⟨⟨hσ.1, hσ.2.le⟩, hσ.1, hσ.2.trans sigmaStar_neg⟩
  have hstar_in : sigmaStar ∈ Ioc (-1 : ℝ) sigmaStar ∩ Ioo (-1) 0 :=
    ⟨⟨by linarith [sigmaStar_gt_neg_half], le_rfl⟩, sigmaStar_mem_Ioo⟩
  ext y
  refine ⟨?_, ?_⟩
  · rintro ⟨σ, hσ, rfl⟩
    rw [← slitBoundaryMap_sigmaStar]
    exact slitBoundaryMap_strictAntiOn_left (hsub hσ) hstar_in hσ.2
  · intro hy
    have hcont : ContinuousOn slitBoundaryMap (Ioo (-1 : ℝ) 0) :=
      continuousOn_slitBoundaryMap_slitPreimage'.mono Set.subset_union_left
    have htend : Tendsto slitBoundaryMap (𝓝[>] (-1 : ℝ)) atTop := by
      unfold slitBoundaryMap
      have hdiv : Tendsto (fun σ : ℝ => (1 - σ) / (-σ * (1 + σ))) (𝓝[>] (-1 : ℝ)) atTop := by
        have hpos : ∀ᶠ σ in 𝓝[>] (-1 : ℝ), 0 < -σ * (1 + σ) := by
          filter_upwards [Ioo_mem_nhdsGT (show (-1 : ℝ) < 0 by norm_num)] with σ hσ
          exact mul_pos (by linarith [hσ.2]) (by linarith [hσ.1])
        have hnum : Tendsto (fun σ : ℝ => 1 - σ) (𝓝[>] (-1 : ℝ)) (𝓝 2) := by
          have : Tendsto (fun σ : ℝ => 1 - σ) (𝓝 (-1 : ℝ)) (𝓝 (1 - (-1))) :=
            (continuous_const.sub continuous_id).tendsto _
          rw [show (1 - (-1) : ℝ) = 2 by norm_num] at this
          exact this.mono_left nhdsWithin_le_nhds
        have hden0 : Tendsto (fun σ : ℝ => -σ * (1 + σ)) (𝓝[>] (-1 : ℝ)) (𝓝 0) := by
          have : Tendsto (fun σ : ℝ => -σ * (1 + σ)) (𝓝 (-1 : ℝ)) (𝓝 (-(-1) * (1 + (-1)))) :=
            (continuous_id.neg.mul (continuous_const.add continuous_id)).tendsto _
          rw [show (-(-1 : ℝ) * (1 + (-1))) = 0 by norm_num] at this
          exact this.mono_left nhdsWithin_le_nhds
        have hinv : Tendsto (fun σ : ℝ => (-σ * (1 + σ))⁻¹) (𝓝[>] (-1 : ℝ)) atTop :=
          tendsto_inv_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.mpr ⟨hden0, hpos⟩)
        refine (hnum.pos_mul_atTop (by norm_num : (0 : ℝ) < 2) hinv).congr fun σ => ?_
        rw [div_eq_mul_inv]
      exact (Real.tendsto_log_atTop.comp hdiv).const_mul_atTop (by positivity)
    obtain ⟨σ₁, hσ₁_gt, hσ₁_mem⟩ := ((htend.eventually (eventually_gt_atTop y)).and
      (Ioo_mem_nhdsGT (show (-1 : ℝ) < sigmaStar from sigmaStar_mem_Ioo.1))).exists
    have hIcc : Icc σ₁ sigmaStar ⊆ Ioo (-1 : ℝ) 0 := fun σ hσ =>
      ⟨hσ₁_mem.1.trans_le hσ.1, hσ.2.trans_lt sigmaStar_neg⟩
    have hmem_y : y ∈ Icc (slitBoundaryMap sigmaStar) (slitBoundaryMap σ₁) :=
      ⟨by rw [slitBoundaryMap_sigmaStar]; exact (show xiStar < y from hy).le, hσ₁_gt.le⟩
    obtain ⟨σ, hσ_Icc, hσ_eq⟩ := intermediate_value_Icc' hσ₁_mem.2.le (hcont.mono hIcc) hmem_y
    refine ⟨σ, ⟨hσ₁_mem.1.trans_le hσ_Icc.1, ?_⟩, hσ_eq⟩
    exact lt_of_le_of_ne hσ_Icc.2 fun h => by
      subst h; rw [slitBoundaryMap_sigmaStar] at hσ_eq; linarith [show xiStar < y from hy]

lemma neg_slitBoundaryMap_strictMonoOn_right :
    StrictMonoOn (fun σ => -slitBoundaryMap σ) (Ici sigmaPlus ∩ Ioi 1) := by
  refine strictMonoOn_of_deriv_pos ((convex_Ici sigmaPlus).inter (convex_Ioi 1)) ?_ ?_
  · exact (continuousOn_slitBoundaryMap_slitPreimage'.mono
      (Set.inter_subset_right.trans Set.subset_union_right)).neg
  · intro σ hσ
    have hmem_s := interior_subset hσ
    have hgt : sigmaPlus < σ := lt_of_le_of_ne hmem_s.1 (fun h => by
      subst h
      obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hσ)
      have hmem := @hsub (sigmaPlus - ε / 2) (Metric.mem_ball.mpr (by
        rw [Real.dist_eq, sub_sub_cancel_left, abs_neg, abs_of_pos (half_pos hε)]; linarith))
      linarith [mem_Ici.mp hmem.1, hε])
    have hd : HasDerivAt (fun τ => -slitBoundaryMap τ)
        (-(-(σ - sigmaStar) * (σ - sigmaPlus) / (2 * π * σ * (σ ^ 2 - 1)))) σ :=
      (hasDerivAt_slitBoundaryMap_Ioi ⟨hmem_s.2, hgt.ne'⟩).neg
    rw [hd.deriv]
    have hnum : 0 < -(-(σ - sigmaStar) * (σ - sigmaPlus)) := by
      have : -(σ - sigmaStar) * (σ - sigmaPlus) < 0 :=
        mul_neg_of_neg_of_pos (by have : 1 < σ := hmem_s.2; linarith [sigmaStar_neg, sigmaPlus_gt_two])
          (by linarith)
      linarith
    have hden : 0 < 2 * π * σ * (σ ^ 2 - 1) := by
      have h1 : 1 < σ := hmem_s.2
      have hsq : 0 < σ ^ 2 - 1 := by nlinarith
      positivity
    change 0 < -(-(σ - sigmaStar) * (σ - sigmaPlus) / (2 * π * σ * (σ ^ 2 - 1)))
    rw [← neg_div]
    exact div_pos hnum hden

lemma neg_slitBoundaryMap_image_Ioi_right :
    (fun σ => -slitBoundaryMap σ) '' Ioi sigmaPlus = Ioi xiStar := by
  have hsub : Ioi sigmaPlus ⊆ Ici sigmaPlus ∩ Ioi 1 := fun σ hσ =>
    have hgt : sigmaPlus < σ := hσ
    ⟨hgt.le, by change 1 < σ; linarith [hgt, sigmaPlus_gt_two]⟩
  have hplus_in : sigmaPlus ∈ Ici sigmaPlus ∩ Ioi 1 := ⟨le_rfl, sigmaPlus_mem_Ioi⟩
  ext y
  refine ⟨?_, ?_⟩
  · rintro ⟨σ, hσ, rfl⟩
    rw [← neg_neg xiStar, ← slitBoundaryMap_sigmaPlus]
    exact neg_slitBoundaryMap_strictMonoOn_right hplus_in (hsub hσ) hσ
  · intro hy
    have hcont : ContinuousOn (fun σ => -slitBoundaryMap σ) (Ioi 1) :=
      (continuousOn_slitBoundaryMap_slitPreimage'.mono Set.subset_union_right).neg
    have htend : Tendsto (fun σ => -slitBoundaryMap σ) atTop atTop := by
      have heq : (fun σ => -slitBoundaryMap σ) =
          fun σ => (2 * π)⁻¹ * (-Real.log ((σ - 1) / (σ * (σ + 1)))) := by
        ext σ; rw [slitBoundaryMap_eq_leftBranch]; ring
      rw [heq]
      have hinv : Tendsto (fun σ : ℝ => (σ - 1) / (σ * (σ + 1))) atTop (𝓝[>] 0) := by
        rw [tendsto_nhdsWithin_iff]
        refine ⟨?_, ?_⟩
        · have heq2 : ∀ᶠ σ : ℝ in atTop, (σ - 1) / (σ * (σ + 1)) = (1 - σ⁻¹) / (σ + 1) := by
            filter_upwards [eventually_gt_atTop (1 : ℝ)] with σ hσ
            field_simp [show σ ≠ 0 by linarith, show σ + 1 ≠ 0 by linarith]
          refine Tendsto.congr' (EventuallyEq.symm heq2) ?_
          have hnum : Tendsto (fun σ : ℝ => 1 - σ⁻¹) atTop (𝓝 1) := by
            have := (tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_inv_atTop_zero
            simpa using this
          have hden : Tendsto (fun σ : ℝ => σ + 1) atTop atTop :=
            tendsto_id.atTop_add tendsto_const_nhds
          simpa using hnum.div_atTop hden
        · filter_upwards [eventually_gt_atTop (1 : ℝ)] with σ hσ
          exact div_pos (by linarith) (by positivity)
      have hlog : Tendsto (fun σ : ℝ => -Real.log ((σ - 1) / (σ * (σ + 1)))) atTop atTop :=
        tendsto_neg_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp hinv)
      exact hlog.const_mul_atTop (by positivity)
    obtain ⟨σ₁, hσ₁_y, hσ₁_gt⟩ := ((htend.eventually (eventually_gt_atTop y)).and
      (eventually_gt_atTop sigmaPlus)).exists
    have hIcc : Icc sigmaPlus σ₁ ⊆ Ioi (1 : ℝ) := fun σ hσ => by
      have hs1 : sigmaPlus ≤ σ := hσ.1
      change 1 < σ; linarith [hs1, sigmaPlus_gt_two]
    have hmem_y : y ∈ Icc (-slitBoundaryMap sigmaPlus) (-slitBoundaryMap σ₁) :=
      ⟨by rw [slitBoundaryMap_sigmaPlus, neg_neg]; exact (show xiStar < y from hy).le, hσ₁_y.le⟩
    obtain ⟨σ, hσ_Icc, hσ_eq⟩ := intermediate_value_Icc hσ₁_gt.le (hcont.mono hIcc) hmem_y
    refine ⟨σ, lt_of_le_of_ne hσ_Icc.1 fun h => by
      subst h; dsimp only at hσ_eq
      rw [slitBoundaryMap_sigmaPlus, neg_neg] at hσ_eq; linarith [show xiStar < y from hy],
      hσ_eq⟩

lemma measurable_slitBoundaryMap : Measurable slitBoundaryMap := by
  unfold slitBoundaryMap; fun_prop

lemma slitBoundaryMap_nonneg_of_mem_Ioo {σ : ℝ} (hσ : σ ∈ Ioo (-1 : ℝ) 0) :
    0 ≤ slitBoundaryMap σ :=
  xiStar_pos.le.trans (xiStar_le_slitBoundaryMap hσ)

lemma slitBoundaryMap_nonpos_of_mem_Ioi {σ : ℝ} (hσ : 1 < σ) :
    slitBoundaryMap σ ≤ 0 :=
  (slitBoundaryMap_le_neg_xiStar hσ).trans (by linarith [xiStar_pos])

lemma setIntegral_rightSlit_eq_Ioi {x y : ℝ} (hy : 0 < y) {φ : ℝ → ℝ}
    (hφ_meas : Measurable φ) (hφ_nn : ∀ t ∈ Ioi xiStar, 0 ≤ φ t)
    (hφ_int : IntegrableOn φ (Ioi xiStar)) :
    IntegrableOn (fun σ : ℝ => (φ (slitBoundaryMap σ) / rightSlitDensity x y σ) * poissonKernel x y σ)
        (Ioo (-1) 0) ∧
      ∫ σ in Ioo (-1) 0, (φ (slitBoundaryMap σ) / rightSlitDensity x y σ) * poissonKernel x y σ =
        ∫ t in Ioi xiStar, φ t := by
  let B' : ℝ → ℝ := fun σ => -(σ - sigmaStar) * (σ - sigmaPlus) / (2 * π * σ * (σ ^ 2 - 1))
  let F : ℝ → ℝ := fun σ => (φ (slitBoundaryMap σ) / rightSlitDensity x y σ) * poissonKernel x y σ
  have hB'_deriv : ∀ σ ∈ Ioo (-1 : ℝ) sigmaStar,
      HasDerivWithinAt slitBoundaryMap (B' σ) (Ioo (-1) sigmaStar) σ := fun σ hσ =>
    (hasDerivAt_slitBoundaryMap ⟨⟨hσ.1, hσ.2.trans sigmaStar_neg⟩, hσ.2.ne⟩).hasDerivWithinAt
  have hB_inj : InjOn slitBoundaryMap (Ioo (-1) sigmaStar) := fun σ₁ hσ₁ σ₂ hσ₂ h =>
    slitBoundaryMap_strictAntiOn_left.injOn
      ⟨⟨hσ₁.1, hσ₁.2.le⟩, hσ₁.1, hσ₁.2.trans sigmaStar_neg⟩
      ⟨⟨hσ₂.1, hσ₂.2.le⟩, hσ₂.1, hσ₂.2.trans sigmaStar_neg⟩ h
  have hpull_B : IntegrableOn (fun σ : ℝ => |B' σ| • φ (slitBoundaryMap σ)) (Ioo (-1) sigmaStar) ∧
      ∫ σ in Ioo (-1) sigmaStar, |B' σ| • φ (slitBoundaryMap σ) = ∫ t in Ioi xiStar, φ t := by
    have hi := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo
      hB'_deriv hB_inj φ).mp (slitBoundaryMap_image_Ioo_left ▸ hφ_int)
    have heq := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hB'_deriv hB_inj φ
    rw [slitBoundaryMap_image_Ioo_left] at heq
    exact ⟨hi, heq.symm⟩
  let S' : ℝ → ℝ := fun σ => -2 / (σ - 1) ^ 2
  have hS_deriv : ∀ σ ∈ Ioo (-1 : ℝ) sigmaStar, HasDerivWithinAt slitInv (S' σ) (Ioo (-1) sigmaStar) σ :=
    fun σ hσ => (hasDerivAt_slitInv (by linarith [hσ.2, sigmaStar_neg])).hasDerivWithinAt
  have hF_meas : Measurable F :=
    ((hφ_meas.comp measurable_slitBoundaryMap).div (by unfold rightSlitDensity poissonKernel slitInv invJacobian; fun_prop)).mul
      (continuous_poissonKernel x hy).measurable
  have hsum_eq : ∀ σ ∈ Ioo (-1 : ℝ) sigmaStar,
      F σ + |S' σ| • F (slitInv σ) = |B' σ| • φ (slitBoundaryMap σ) := by
    intro σ hσ
    have hIoo : σ ∈ Ioo (-1 : ℝ) 0 := ⟨hσ.1, hσ.2.trans sigmaStar_neg⟩
    have hs1 : σ ≠ 1 := by linarith [hIoo.2]
    have hR_pos : 0 < rightSlitDensity x y σ := rightSlitDensity_pos hy ⟨hIoo, hσ.2.ne⟩
    have hJ_pos : 0 < invJacobian σ := invJacobian_pos_left ⟨hIoo, hσ.2.ne⟩
    have hS_abs : |S' σ| = 2 / (σ - 1) ^ 2 := by
      dsimp [S']
      rw [abs_div, abs_neg, abs_of_pos (by norm_num), abs_of_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr hs1))]
    have hR_eq : rightSlitDensity x y σ =
        (poissonKernel x y σ + |S' σ| * poissonKernel x y (slitInv σ)) * invJacobian σ := by
      unfold rightSlitDensity
      rw [invJacobian_slitInv hIoo, hS_abs]
      ring
    have hB_abs : |B' σ| = (invJacobian σ)⁻¹ := by
      rw [invJacobian_eq_inv_abs_deriv, inv_inv]
    dsimp [F]
    rw [slitBoundaryMap_slitInv hIoo, rightSlitDensity_slitInv hs1, hB_abs]
    calc (φ (slitBoundaryMap σ) / rightSlitDensity x y σ) * poissonKernel x y σ +
          |S' σ| * ((φ (slitBoundaryMap σ) / rightSlitDensity x y σ) * poissonKernel x y (slitInv σ))
        = (φ (slitBoundaryMap σ) / rightSlitDensity x y σ) *
            (poissonKernel x y σ + |S' σ| * poissonKernel x y (slitInv σ)) := by ring
      _ = (φ (slitBoundaryMap σ) / ((poissonKernel x y σ + |S' σ| * poissonKernel x y (slitInv σ)) *
            invJacobian σ)) * (poissonKernel x y σ + |S' σ| * poissonKernel x y (slitInv σ)) := by
          rw [← hR_eq]
      _ = (invJacobian σ)⁻¹ * φ (slitBoundaryMap σ) := by
          have hsum_pos : 0 < poissonKernel x y σ + |S' σ| * poissonKernel x y (slitInv σ) := by
            have h1 := poissonKernel_pos (x := x) hy σ
            have h2 : 0 ≤ |S' σ| * poissonKernel x y (slitInv σ) :=
              mul_nonneg (abs_nonneg _) (poissonKernel_nonneg hy.le _)
            linarith
          field_simp [hsum_pos.ne', hJ_pos.ne']
  have hF_left : IntegrableOn F (Ioo (-1) sigmaStar) := by
    refine hpull_B.1.mono' hF_meas.aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioo]
    refine Eventually.of_forall fun σ hσ => ?_
    have hIoo : σ ∈ Ioo (-1 : ℝ) 0 := ⟨hσ.1, hσ.2.trans sigmaStar_neg⟩
    have hB_mem : slitBoundaryMap σ ∈ Ioi xiStar := slitBoundaryMap_image_Ioo_left ▸ mem_image_of_mem _ hσ
    have hφ_ge : 0 ≤ φ (slitBoundaryMap σ) := hφ_nn _ hB_mem
    have hF_nn : 0 ≤ F σ := mul_nonneg (div_nonneg hφ_ge (rightSlitDensity_nonneg' x hy.le σ))
      (poissonKernel_nonneg hy.le σ)
    have hF2_nn : 0 ≤ |S' σ| • F (slitInv σ) := by
      rw [smul_eq_mul]; dsimp [F]
      rw [slitBoundaryMap_slitInv hIoo, rightSlitDensity_slitInv (by linarith [hIoo.2])]
      exact mul_nonneg (abs_nonneg _) (mul_nonneg (div_nonneg hφ_ge (rightSlitDensity_nonneg' x hy.le σ))
        (poissonKernel_nonneg hy.le _))
    rw [Real.norm_of_nonneg hF_nn]
    linarith [hsum_eq σ hσ]
  have hF2_left : IntegrableOn (fun σ => |S' σ| • F (slitInv σ)) (Ioo (-1) sigmaStar) := by
    have hmeas2 : Measurable (fun σ => |S' σ| • F (slitInv σ)) :=
      ((measurable_const.div ((measurable_id.sub_const 1).pow_const 2)).abs).mul
        (hF_meas.comp (by unfold slitInv; fun_prop))
    refine hpull_B.1.mono' hmeas2.aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioo]
    refine Eventually.of_forall fun σ hσ => ?_
    have hIoo : σ ∈ Ioo (-1 : ℝ) 0 := ⟨hσ.1, hσ.2.trans sigmaStar_neg⟩
    have hB_mem : slitBoundaryMap σ ∈ Ioi xiStar := slitBoundaryMap_image_Ioo_left ▸ mem_image_of_mem _ hσ
    have hφ_ge : 0 ≤ φ (slitBoundaryMap σ) := hφ_nn _ hB_mem
    have hF_nn : 0 ≤ F σ := mul_nonneg (div_nonneg hφ_ge (rightSlitDensity_nonneg' x hy.le σ))
      (poissonKernel_nonneg hy.le σ)
    have hF2_nn : 0 ≤ |S' σ| • F (slitInv σ) := by
      rw [smul_eq_mul]; dsimp [F]
      rw [slitBoundaryMap_slitInv hIoo, rightSlitDensity_slitInv (by linarith [hIoo.2])]
      exact mul_nonneg (abs_nonneg _) (mul_nonneg (div_nonneg hφ_ge (rightSlitDensity_nonneg' x hy.le σ))
        (poissonKernel_nonneg hy.le _))
    rw [Real.norm_of_nonneg hF2_nn]
    linarith [hsum_eq σ hσ]
  have hF_right : IntegrableOn F (Ioo sigmaStar 0) :=
    (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo
      hS_deriv injOn_slitInv_Ioo F).mpr hF2_left |> fun h => slitInv_image_Ioo_left ▸ h
  have hF_right_val : ∫ σ in Ioo sigmaStar 0, F σ =
      ∫ σ in Ioo (-1) sigmaStar, |S' σ| • F (slitInv σ) := by
    rw [← slitInv_image_Ioo_left]
    exact integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hS_deriv injOn_slitInv_Ioo F
  have hunion_ae : (Ioo (-1 : ℝ) sigmaStar ∪ Ioo sigmaStar 0 : Set ℝ) =ᵐ[volume] Ioo (-1) 0 := by
    have hnull : volume ({sigmaStar} : Set ℝ) = 0 := ({sigmaStar} : Set ℝ).toFinite.measure_zero volume
    change ∀ᵐ σ ∂volume, (σ ∈ Ioo (-1 : ℝ) sigmaStar ∪ Ioo sigmaStar 0) = (σ ∈ Ioo (-1 : ℝ) 0)
    rw [ae_iff]
    refine measure_mono_null (fun σ hσ => ?_) hnull
    rw [mem_singleton_iff]
    by_contra hne
    apply hσ
    apply propext
    have hs := sigmaStar_mem_Ioo
    simp only [mem_union, mem_Ioo]
    constructor
    · rintro (h | h)
      · exact ⟨h.1, h.2.trans hs.2⟩
      · exact ⟨hs.1.trans h.1, h.2⟩
    · intro h
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact Or.inl ⟨h.1, hlt⟩
      · exact Or.inr ⟨hgt, h.2⟩
  have hF_all : IntegrableOn F (Ioo (-1) 0) :=
    (hF_left.union hF_right).congr_set_ae hunion_ae.symm
  refine ⟨hF_all, ?_⟩
  have hdisj : Disjoint (Ioo (-1 : ℝ) sigmaStar) (Ioo sigmaStar 0) := by
    rw [Set.disjoint_left]; intro σ h1 h2; linarith [h1.2, h2.1]
  calc ∫ σ in Ioo (-1) 0, F σ
      = ∫ σ in Ioo (-1) sigmaStar ∪ Ioo sigmaStar 0, F σ :=
        (setIntegral_congr_set hunion_ae).symm
    _ = (∫ σ in Ioo (-1) sigmaStar, F σ) + (∫ σ in Ioo sigmaStar 0, F σ) :=
        setIntegral_union hdisj measurableSet_Ioo hF_left hF_right
    _ = (∫ σ in Ioo (-1) sigmaStar, F σ) +
          (∫ σ in Ioo (-1) sigmaStar, |S' σ| • F (slitInv σ)) := by rw [hF_right_val]
    _ = ∫ σ in Ioo (-1) sigmaStar, (F σ + |S' σ| • F (slitInv σ)) :=
        (integral_add hF_left hF2_left).symm
    _ = ∫ σ in Ioo (-1) sigmaStar, |B' σ| • φ (slitBoundaryMap σ) :=
        setIntegral_congr_fun measurableSet_Ioo hsum_eq
    _ = ∫ t in Ioi xiStar, φ t := hpull_B.2

lemma setIntegral_leftSlit_eq_Ioi {x y : ℝ} (hy : 0 < y) {φ : ℝ → ℝ}
    (hφ_meas : Measurable φ) (hφ_nn : ∀ t ∈ Ioi xiStar, 0 ≤ φ t)
    (hφ_int : IntegrableOn φ (Ioi xiStar)) :
    IntegrableOn (fun σ : ℝ => (φ (-slitBoundaryMap σ) / leftSlitDensity x y σ) * poissonKernel x y σ)
        (Ioi 1) ∧
      ∫ σ in Ioi 1, (φ (-slitBoundaryMap σ) / leftSlitDensity x y σ) * poissonKernel x y σ =
        ∫ t in Ioi xiStar, φ t := by
  let B' : ℝ → ℝ := fun σ => -(-(σ - sigmaStar) * (σ - sigmaPlus) / (2 * π * σ * (σ ^ 2 - 1)))
  let F : ℝ → ℝ := fun σ => (φ (-slitBoundaryMap σ) / leftSlitDensity x y σ) * poissonKernel x y σ
  have hB'_deriv : ∀ σ ∈ Ioi sigmaPlus,
      HasDerivWithinAt (fun τ => -slitBoundaryMap τ) (B' σ) (Ioi sigmaPlus) σ := fun σ hσ => by
    have hgt1 : 1 < σ := by linarith [sigmaPlus_gt_two, show sigmaPlus < σ from hσ]
    exact (hasDerivAt_slitBoundaryMap_Ioi ⟨hgt1, hσ.ne'⟩).neg.hasDerivWithinAt
  have hB_inj : InjOn (fun τ => -slitBoundaryMap τ) (Ioi sigmaPlus) := fun σ₁ hσ₁ σ₂ hσ₂ h => by
    have hs1 : sigmaPlus < σ₁ := hσ₁
    have hs2 : sigmaPlus < σ₂ := hσ₂
    exact neg_slitBoundaryMap_strictMonoOn_right.injOn
      ⟨hs1.le, by change 1 < σ₁; linarith [sigmaPlus_gt_two]⟩
      ⟨hs2.le, by change 1 < σ₂; linarith [sigmaPlus_gt_two]⟩ h
  have hpull_B : IntegrableOn (fun σ : ℝ => |B' σ| • φ (-slitBoundaryMap σ)) (Ioi sigmaPlus) ∧
      ∫ σ in Ioi sigmaPlus, |B' σ| • φ (-slitBoundaryMap σ) = ∫ t in Ioi xiStar, φ t := by
    have hi := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
      hB'_deriv hB_inj φ).mp (neg_slitBoundaryMap_image_Ioi_right ▸ hφ_int)
    have heq := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hB'_deriv hB_inj φ
    rw [neg_slitBoundaryMap_image_Ioi_right] at heq
    exact ⟨hi, heq.symm⟩
  let S' : ℝ → ℝ := fun σ => -2 / (σ - 1) ^ 2
  have hS_deriv : ∀ σ ∈ Ioi sigmaPlus, HasDerivWithinAt leftSlitInv (S' σ) (Ioi sigmaPlus) σ :=
    fun σ hσ => (hasDerivAt_leftSlitInv (by linarith [sigmaPlus_gt_two, show sigmaPlus < σ from hσ])).hasDerivWithinAt
  have hF_meas : Measurable F :=
    ((hφ_meas.comp measurable_slitBoundaryMap.neg).div
      (by unfold leftSlitDensity poissonKernel leftSlitInv invJacobian; fun_prop)).mul
      (continuous_poissonKernel x hy).measurable
  have hsum_eq : ∀ σ ∈ Ioi sigmaPlus,
      F σ + |S' σ| • F (leftSlitInv σ) = |B' σ| • φ (-slitBoundaryMap σ) := by
    intro σ hσ
    have hgt1 : 1 < σ := by linarith [sigmaPlus_gt_two, show sigmaPlus < σ from hσ]
    have hs1 : σ ≠ 1 := hgt1.ne'
    have hL_pos : 0 < leftSlitDensity x y σ := leftSlitDensity_pos hy ⟨hgt1, hσ.ne'⟩
    have hJ_pos : 0 < invJacobian σ := invJacobian_pos_right ⟨hgt1, hσ.ne'⟩
    have hS_abs : |S' σ| = 2 / (σ - 1) ^ 2 := by
      dsimp [S']
      rw [abs_div, abs_neg, abs_of_pos (by norm_num), abs_of_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr hs1))]
    have hL_eq : leftSlitDensity x y σ =
        (poissonKernel x y σ + |S' σ| * poissonKernel x y (leftSlitInv σ)) * invJacobian σ := by
      unfold leftSlitDensity
      rw [invJacobian_leftSlitInv hgt1, hS_abs]
      ring
    have hB_abs : |B' σ| = (invJacobian σ)⁻¹ := by
      dsimp [B']; rw [abs_neg, invJacobian_eq_inv_abs_deriv, inv_inv]
    dsimp [F]
    rw [slitBoundaryMap_leftSlitInv hgt1, leftSlitDensity_leftSlitInv hs1, hB_abs]
    calc (φ (-slitBoundaryMap σ) / leftSlitDensity x y σ) * poissonKernel x y σ +
          |S' σ| * ((φ (-slitBoundaryMap σ) / leftSlitDensity x y σ) * poissonKernel x y (leftSlitInv σ))
        = (φ (-slitBoundaryMap σ) / leftSlitDensity x y σ) *
            (poissonKernel x y σ + |S' σ| * poissonKernel x y (leftSlitInv σ)) := by ring
      _ = (invJacobian σ)⁻¹ * φ (-slitBoundaryMap σ) := by
          rw [hL_eq]
          have hsum_pos : 0 < poissonKernel x y σ + |S' σ| * poissonKernel x y (leftSlitInv σ) := by
            have h1 := poissonKernel_pos (x := x) hy σ
            have h2 : 0 ≤ |S' σ| * poissonKernel x y (leftSlitInv σ) :=
              mul_nonneg (abs_nonneg _) (poissonKernel_nonneg hy.le _)
            linarith
          field_simp [hsum_pos.ne', hJ_pos.ne']
  have hF_right : IntegrableOn F (Ioi sigmaPlus) := by
    refine hpull_B.1.mono' hF_meas.aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun σ hσ => ?_
    have hB_mem : -slitBoundaryMap σ ∈ Ioi xiStar :=
      neg_slitBoundaryMap_image_Ioi_right ▸ mem_image_of_mem _ hσ
    have hφ_ge : 0 ≤ φ (-slitBoundaryMap σ) := hφ_nn _ hB_mem
    have hF_nn : 0 ≤ F σ := mul_nonneg (div_nonneg hφ_ge (leftSlitDensity_nonneg' x hy.le σ))
      (poissonKernel_nonneg hy.le σ)
    have hgt1 : 1 < σ := by linarith [sigmaPlus_gt_two, show sigmaPlus < σ from hσ]
    have hF2_nn : 0 ≤ |S' σ| • F (leftSlitInv σ) := by
      rw [smul_eq_mul]; dsimp [F]
      rw [slitBoundaryMap_leftSlitInv hgt1, leftSlitDensity_leftSlitInv hgt1.ne']
      exact mul_nonneg (abs_nonneg _) (mul_nonneg (div_nonneg hφ_ge (leftSlitDensity_nonneg' x hy.le σ))
        (poissonKernel_nonneg hy.le _))
    rw [Real.norm_of_nonneg hF_nn]
    linarith [hsum_eq σ hσ]
  have hF2_right : IntegrableOn (fun σ => |S' σ| • F (leftSlitInv σ)) (Ioi sigmaPlus) := by
    have hmeas2 : Measurable (fun σ => |S' σ| • F (leftSlitInv σ)) :=
      ((measurable_const.div ((measurable_id.sub_const 1).pow_const 2)).abs).mul
        (hF_meas.comp (by unfold leftSlitInv; fun_prop))
    refine hpull_B.1.mono' hmeas2.aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun σ hσ => ?_
    have hB_mem : -slitBoundaryMap σ ∈ Ioi xiStar :=
      neg_slitBoundaryMap_image_Ioi_right ▸ mem_image_of_mem _ hσ
    have hφ_ge : 0 ≤ φ (-slitBoundaryMap σ) := hφ_nn _ hB_mem
    have hgt1 : 1 < σ := by linarith [sigmaPlus_gt_two, show sigmaPlus < σ from hσ]
    have hF_nn : 0 ≤ F σ := mul_nonneg (div_nonneg hφ_ge (leftSlitDensity_nonneg' x hy.le σ))
      (poissonKernel_nonneg hy.le σ)
    have hF2_nn : 0 ≤ |S' σ| • F (leftSlitInv σ) := by
      rw [smul_eq_mul]; dsimp [F]
      rw [slitBoundaryMap_leftSlitInv hgt1, leftSlitDensity_leftSlitInv hgt1.ne']
      exact mul_nonneg (abs_nonneg _) (mul_nonneg (div_nonneg hφ_ge (leftSlitDensity_nonneg' x hy.le σ))
        (poissonKernel_nonneg hy.le _))
    rw [Real.norm_of_nonneg hF2_nn]
    linarith [hsum_eq σ hσ]
  have hF_left : IntegrableOn F (Ioo 1 sigmaPlus) :=
    (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
      hS_deriv injOn_leftSlitInv_Ioi F).mpr hF2_right |> fun h => leftSlitInv_image_Ioi_right ▸ h
  have hF_left_val : ∫ σ in Ioo 1 sigmaPlus, F σ =
      ∫ σ in Ioi sigmaPlus, |S' σ| • F (leftSlitInv σ) := by
    rw [← leftSlitInv_image_Ioi_right]
    exact integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hS_deriv injOn_leftSlitInv_Ioi F
  have hunion_ae : (Ioo (1 : ℝ) sigmaPlus ∪ Ioi sigmaPlus : Set ℝ) =ᵐ[volume] Ioi 1 := by
    have hnull : volume ({sigmaPlus} : Set ℝ) = 0 := ({sigmaPlus} : Set ℝ).toFinite.measure_zero volume
    change ∀ᵐ σ ∂volume, (σ ∈ Ioo (1 : ℝ) sigmaPlus ∪ Ioi sigmaPlus) = (σ ∈ Ioi 1)
    rw [ae_iff]
    refine measure_mono_null (fun σ hσ => ?_) hnull
    rw [mem_singleton_iff]
    by_contra hne
    apply hσ
    apply propext
    simp only [mem_union, mem_Ioo, mem_Ioi]
    constructor
    · rintro (h | h)
      · exact h.1
      · linarith [sigmaPlus_gt_two]
    · intro h
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact Or.inl ⟨h, hlt⟩
      · exact Or.inr hgt
  have hF_all : IntegrableOn F (Ioi 1) :=
    (hF_left.union hF_right).congr_set_ae hunion_ae.symm
  refine ⟨hF_all, ?_⟩
  have hdisj : Disjoint (Ioo (1 : ℝ) sigmaPlus) (Ioi sigmaPlus) := by
    rw [Set.disjoint_left]; intro σ h1 h2; linarith [h1.2, show sigmaPlus < σ from h2]
  calc ∫ σ in Ioi 1, F σ
      = ∫ σ in Ioo 1 sigmaPlus ∪ Ioi sigmaPlus, F σ :=
        (setIntegral_congr_set hunion_ae).symm
    _ = (∫ σ in Ioo 1 sigmaPlus, F σ) + (∫ σ in Ioi sigmaPlus, F σ) :=
        setIntegral_union hdisj measurableSet_Ioi hF_left hF_right
    _ = (∫ σ in Ioi sigmaPlus, |S' σ| • F (leftSlitInv σ)) +
          (∫ σ in Ioi sigmaPlus, F σ) := by rw [hF_left_val]
    _ = ∫ σ in Ioi sigmaPlus, (F σ + |S' σ| • F (leftSlitInv σ)) := by
        rw [add_comm, integral_add hF_right hF2_right]
    _ = ∫ σ in Ioi sigmaPlus, |B' σ| • φ (-slitBoundaryMap σ) :=
        setIntegral_congr_fun measurableSet_Ioi hsum_eq
    _ = ∫ t in Ioi xiStar, φ t := hpull_B.2

noncomputable def slitDensity (x y σ : ℝ) : ℝ :=
  if σ < 0 then rightSlitDensity x y σ else leftSlitDensity x y σ

lemma slitDensity_pos_ae {x y : ℝ} (hy : 0 < y) :
    ∀ᵐ σ ∂(volume.restrict slitPreimage), 0 < slitDensity x y σ := by
  have hnull : volume ({sigmaStar, sigmaPlus} : Set ℝ) = 0 :=
    (({sigmaStar, sigmaPlus} : Set ℝ).toFinite).measure_zero volume
  change ∀ᵐ σ ∂(volume.restrict (Ioo (-1 : ℝ) 0 ∪ Ioi 1)), 0 < slitDensity x y σ
  rw [ae_restrict_iff' (measurableSet_Ioo.union measurableSet_Ioi)]
  filter_upwards [compl_mem_ae_iff.mpr hnull] with σ hnot hmem
  simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] at hnot
  unfold slitDensity
  rcases hmem with hIoo | hIoi
  · rw [if_pos hIoo.2]
    exact rightSlitDensity_pos hy ⟨hIoo, hnot.1⟩
  · rw [if_neg (by linarith [show 1 < σ from hIoi])]
    exact leftSlitDensity_pos hy ⟨hIoi, hnot.2⟩

theorem setIntegral_slitPreimage_div_slitDensity {x y : ℝ} (hy : 0 < y) {φ : ℝ → ℝ}
    (hφ_meas : Measurable φ) (hφ_nn : ∀ t ∈ Ioi xiStar, 0 ≤ φ t)
    (hφ_int : IntegrableOn φ (Ioi xiStar)) :
    IntegrableOn
        (fun σ : ℝ => (φ |slitBoundaryMap σ| / slitDensity x y σ) * poissonKernel x y σ)
        slitPreimage ∧
      ∫ σ in slitPreimage,
          (φ |slitBoundaryMap σ| / slitDensity x y σ) * poissonKernel x y σ =
        2 * ∫ t in Ioi xiStar, φ t := by
  obtain ⟨hR_int, hR_eq⟩ := setIntegral_rightSlit_eq_Ioi (x := x) hy hφ_meas hφ_nn hφ_int
  obtain ⟨hL_int, hL_eq⟩ := setIntegral_leftSlit_eq_Ioi (x := x) hy hφ_meas hφ_nn hφ_int
  have hcongrR : EqOn
      (fun σ : ℝ => (φ (slitBoundaryMap σ) / rightSlitDensity x y σ) * poissonKernel x y σ)
      (fun σ : ℝ => (φ |slitBoundaryMap σ| / slitDensity x y σ) * poissonKernel x y σ)
      (Ioo (-1) 0) := fun σ hσ => by
    dsimp only
    rw [abs_of_nonneg (slitBoundaryMap_nonneg_of_mem_Ioo hσ), slitDensity, if_pos hσ.2]
  have hcongrL : EqOn
      (fun σ : ℝ => (φ (-slitBoundaryMap σ) / leftSlitDensity x y σ) * poissonKernel x y σ)
      (fun σ : ℝ => (φ |slitBoundaryMap σ| / slitDensity x y σ) * poissonKernel x y σ)
      (Ioi 1) := fun σ hσ => by
    dsimp only
    rw [abs_of_nonpos (slitBoundaryMap_nonpos_of_mem_Ioi hσ), slitDensity,
      if_neg (by linarith [show 1 < σ from hσ])]
  have hIoo : IntegrableOn
      (fun σ : ℝ => (φ |slitBoundaryMap σ| / slitDensity x y σ) * poissonKernel x y σ)
      (Ioo (-1) 0) := hR_int.congr_fun hcongrR measurableSet_Ioo
  have hIoi : IntegrableOn
      (fun σ : ℝ => (φ |slitBoundaryMap σ| / slitDensity x y σ) * poissonKernel x y σ)
      (Ioi 1) := hL_int.congr_fun hcongrL measurableSet_Ioi
  have hdisj : Disjoint (Ioo (-1 : ℝ) 0) (Ioi 1) := by
    rw [Set.disjoint_left]; intro σ h1 h2; linarith [h1.2, show 1 < σ from h2]
  refine ⟨hIoo.union hIoi, ?_⟩
  unfold slitPreimage
  rw [setIntegral_union hdisj measurableSet_Ioi hIoo hIoi,
    setIntegral_congr_fun measurableSet_Ioo hcongrR.symm,
    setIntegral_congr_fun measurableSet_Ioi hcongrL.symm, hR_eq, hL_eq]
  ring

private lemma abs_log_le_max_of_bounds {a u b : ℝ} (ha : 0 < a) (hau : a ≤ u) (hub : u ≤ b) :
    |Real.log u| ≤ |Real.log a| + |Real.log b| := by
  have hu : 0 < u := ha.trans_le hau
  have hb : 0 < b := hu.trans_le hub
  rw [abs_le]
  constructor
  · have h1 := Real.log_le_log ha hau
    linarith [neg_abs_le (Real.log a), abs_nonneg (Real.log b)]
  · have h2 := Real.log_le_log hu hub
    linarith [le_abs_self (Real.log b), abs_nonneg (Real.log a)]

private lemma rightSlitDensity_lower {x y σ : ℝ} (hy : 0 < y) (hσ : σ ∈ Ioo (-1 : ℝ) 0)
    (hs : σ ≠ sigmaStar) :
    (y / (π * ((|x| + 1) ^ 2 + y ^ 2))) * (π / 4) * |σ| * |σ + 1| ≤
      rightSlitDensity x y σ := by
  have hP_lo : y / (π * ((|x| + 1) ^ 2 + y ^ 2)) ≤ poissonKernel x y σ := by
    unfold poissonKernel
    have hlt1 : |σ| < 1 := abs_lt.mpr ⟨hσ.1, by linarith [hσ.2]⟩
    have h1 : |σ - x| ≤ |x| + 1 := by
      calc |σ - x| ≤ |σ| + |x| := abs_sub _ _
        _ ≤ 1 + |x| := by linarith
        _ = |x| + 1 := by ring
    have hsq : (σ - x) ^ 2 ≤ (|x| + 1) ^ 2 := by
      rw [← sq_abs (σ - x)]
      exact sq_le_sq' (by linarith [abs_nonneg (σ - x)]) h1
    gcongr
  have hJ_lo : (π / 4) * |σ| * |σ + 1| ≤ invJacobian σ := by
    unfold invJacobian
    have hstar_le : |σ - sigmaStar| ≤ 2 := by
      rw [abs_le]; constructor <;> linarith [hσ.1, hσ.2, sigmaStar_gt_neg_half, sigmaStar_neg]
    have hplus_le : |σ - sigmaPlus| ≤ 4 := by
      rw [abs_le]; constructor <;> linarith [hσ.1, hσ.2, sigmaPlus_gt_two, sigmaPlus_lt_242]
    have h1ms : 1 ≤ |1 - σ| := by rw [abs_of_pos (by linarith [hσ.2])]; linarith [hσ.2]
    have hden_pos : 0 < |σ - sigmaStar| * |σ - sigmaPlus| :=
      mul_pos (abs_pos.mpr (sub_ne_zero.mpr hs))
        (abs_pos.mpr (by linarith [hσ.2, sigmaPlus_gt_two]))
    have hnum : |σ * (σ ^ 2 - 1)| = |σ| * |σ + 1| * |1 - σ| := by
      rw [show σ * (σ ^ 2 - 1) = -(σ * (σ + 1) * (1 - σ)) by ring, abs_neg, abs_mul, abs_mul]
    calc (π / 4) * |σ| * |σ + 1|
        = 2 * π * (|σ| * |σ + 1| * 1) / (2 * 4) := by ring
      _ ≤ 2 * π * (|σ| * |σ + 1| * |1 - σ|) / (|σ - sigmaStar| * |σ - sigmaPlus|) := by
          gcongr
      _ = 2 * π * |σ * (σ ^ 2 - 1)| / (|σ - sigmaStar| * |σ - sigmaPlus|) := by rw [hnum]
  have hP0 : 0 ≤ y / (π * ((|x| + 1) ^ 2 + y ^ 2)) := by positivity
  have hJ0 : 0 ≤ (π / 4) * |σ| * |σ + 1| := by positivity
  have h1 : (y / (π * ((|x| + 1) ^ 2 + y ^ 2))) * ((π / 4) * |σ| * |σ + 1|) ≤
      poissonKernel x y σ * invJacobian σ :=
    mul_le_mul hP_lo hJ_lo hJ0 (poissonKernel_nonneg hy.le σ)
  have h2 : 0 ≤ poissonKernel x y (slitInv σ) * invJacobian (slitInv σ) :=
    mul_nonneg (poissonKernel_nonneg hy.le _) (invJacobian_nonneg' _)
  unfold rightSlitDensity
  linarith

private lemma rightSlitDensity_upper' {x y σ : ℝ} (hy : 0 < y) (hσ : σ ∈ Ioo (-1 : ℝ) 0) :
    rightSlitDensity x y σ ≤ (2.61 * (1 + √2) / (π * y)) / |σ - sigmaStar| := by
  by_cases hne : σ = sigmaStar
  · subst hne; unfold rightSlitDensity; rw [slitInv_sigmaStar]; unfold invJacobian; simp
  · unfold rightSlitDensity
    have hP1 := poissonKernel_le_inv_pi_mul_y (x := x) hy σ
    have hP2 := poissonKernel_le_inv_pi_mul_y (x := x) hy (slitInv σ)
    have hJ1 := invJacobian_le ⟨hσ, hne⟩
    have hslit_Ioo : slitInv σ ∈ Ioo (-1 : ℝ) 0 := slitInv_mem_Ioo hσ
    have hslit_ne : slitInv σ ≠ sigmaStar := by
      rw [← sub_ne_zero, slitInv_sub_sigmaStar_eq (by linarith [hσ.2])]
      exact div_ne_zero (mul_ne_zero (neg_ne_zero.mpr (by positivity)) (sub_ne_zero.mpr hne))
        (by linarith [hσ.2])
    have hJ2 : invJacobian (slitInv σ) ≤ 2.61 * √2 / |σ - sigmaStar| := by
      have hstar : 0 < |σ - sigmaStar| := abs_pos.mpr (sub_ne_zero.mpr hne)
      calc invJacobian (slitInv σ) ≤ 2.61 / |slitInv σ - sigmaStar| :=
            invJacobian_le ⟨hslit_Ioo, hslit_ne⟩
        _ ≤ 2.61 / (|σ - sigmaStar| / √2) := by gcongr; exact abs_slitInv_sub_sigmaStar_lower hσ
        _ = 2.61 * √2 / |σ - sigmaStar| := by rw [div_div_eq_mul_div]
    have hterm1 : poissonKernel x y σ * invJacobian σ ≤ (1 / (π * y)) * (2.61 / |σ - sigmaStar|) :=
      mul_le_mul hP1 hJ1 (invJacobian_nonneg' _) (by positivity)
    have hterm2 : poissonKernel x y (slitInv σ) * invJacobian (slitInv σ) ≤
        (1 / (π * y)) * (2.61 * √2 / |σ - sigmaStar|) :=
      mul_le_mul hP2 hJ2 (invJacobian_nonneg' _) (by positivity)
    calc poissonKernel x y σ * invJacobian σ +
          poissonKernel x y (slitInv σ) * invJacobian (slitInv σ)
        ≤ (1 / (π * y)) * (2.61 / |σ - sigmaStar|) +
            (1 / (π * y)) * (2.61 * √2 / |σ - sigmaStar|) := add_le_add hterm1 hterm2
      _ = (2.61 * (1 + √2) / (π * y)) / |σ - sigmaStar| := by ring

private lemma leftSlitDensity_lower {x y σ : ℝ} (hy : 0 < y) (hσ : 1 < σ)
    (hp : σ ≠ sigmaPlus) :
    (y / (π * ((1 + |x|) ^ 2 + y ^ 2))) * (2 * π / 3) * |σ - 1| / |σ + 1| ^ 3 ≤
      leftSlitDensity x y σ := by
  have hsp1_pos : 0 < σ + 1 := by linarith
  have hP_lo : y / (π * ((1 + |x|) ^ 2 + y ^ 2)) / |σ + 1| ^ 2 ≤ poissonKernel x y σ := by
    unfold poissonKernel
    have h1 : |σ - x| ≤ (1 + |x|) * |σ + 1| := by
      have hab : |σ - x| ≤ σ + |x| := by
        calc |σ - x| ≤ |σ| + |x| := abs_sub _ _
          _ = σ + |x| := by rw [abs_of_pos (by linarith)]
      have h2 : σ + |x| ≤ (1 + |x|) * (σ + 1) := by nlinarith [abs_nonneg x]
      rw [abs_of_pos hsp1_pos]
      exact hab.trans h2
    have hsq : (σ - x) ^ 2 ≤ (1 + |x|) ^ 2 * |σ + 1| ^ 2 := by
      rw [← sq_abs (σ - x), ← mul_pow]
      exact sq_le_sq' (by linarith [abs_nonneg (σ - x)]) h1
    have hy_le : y ^ 2 ≤ y ^ 2 * |σ + 1| ^ 2 := by
      have h1_le : 1 ≤ |σ + 1| ^ 2 := by
        rw [abs_of_pos hsp1_pos]; nlinarith
      exact le_mul_of_one_le_right (sq_nonneg y) h1_le
    have hden_le : (σ - x) ^ 2 + y ^ 2 ≤ ((1 + |x|) ^ 2 + y ^ 2) * |σ + 1| ^ 2 := by
      linarith [hsq, hy_le]
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    calc y * (π * ((σ - x) ^ 2 + y ^ 2))
        = π * y * ((σ - x) ^ 2 + y ^ 2) := by ring
      _ ≤ π * y * (((1 + |x|) ^ 2 + y ^ 2) * |σ + 1| ^ 2) := by gcongr
      _ = y * (π * ((1 + |x|) ^ 2 + y ^ 2) * |σ + 1| ^ 2) := by ring
  have hJ_lo : (2 * π / 3) * |σ - 1| / |σ + 1| ≤ invJacobian σ := by
    unfold invJacobian
    have hstar_le : |σ - sigmaStar| ≤ |σ + 1| := by
      rw [abs_of_pos (by linarith [sigmaStar_neg]), abs_of_pos hsp1_pos]
      linarith [sigmaStar_gt_neg_half]
    have hplus_le : |σ - sigmaPlus| ≤ 3 * |σ + 1| := by
      rw [abs_of_pos hsp1_pos, abs_le]; constructor <;>
        linarith [sigmaPlus_gt_two, sigmaPlus_lt_242]
    have hnum : |σ * (σ ^ 2 - 1)| = σ * |σ - 1| * |σ + 1| := by
      rw [show σ * (σ ^ 2 - 1) = σ * (σ - 1) * (σ + 1) by ring, abs_mul, abs_mul,
        abs_of_pos (by linarith)]
    have hden_pos : 0 < |σ - sigmaStar| * |σ - sigmaPlus| :=
      mul_pos (abs_pos.mpr (by linarith [sigmaStar_neg])) (abs_pos.mpr (sub_ne_zero.mpr hp))
    calc (2 * π / 3) * |σ - 1| / |σ + 1|
        = 2 * π * (1 * |σ - 1| * |σ + 1|) / (|σ + 1| * (3 * |σ + 1|)) := by
          field_simp [hsp1_pos.ne']
      _ ≤ 2 * π * (σ * |σ - 1| * |σ + 1|) / (|σ - sigmaStar| * |σ - sigmaPlus|) := by
          gcongr
      _ = 2 * π * |σ * (σ ^ 2 - 1)| / (|σ - sigmaStar| * |σ - sigmaPlus|) := by rw [hnum]
  have h1 : (y / (π * ((1 + |x|) ^ 2 + y ^ 2)) / |σ + 1| ^ 2) * ((2 * π / 3) * |σ - 1| / |σ + 1|) ≤
      poissonKernel x y σ * invJacobian σ :=
    mul_le_mul hP_lo hJ_lo (by positivity) (poissonKernel_nonneg hy.le σ)
  have h2 : 0 ≤ poissonKernel x y (leftSlitInv σ) * invJacobian (leftSlitInv σ) :=
    mul_nonneg (poissonKernel_nonneg hy.le _) (invJacobian_nonneg' _)
  have hcalc : (y / (π * ((1 + |x|) ^ 2 + y ^ 2)) / |σ + 1| ^ 2) * ((2 * π / 3) * |σ - 1| / |σ + 1|) =
      (y / (π * ((1 + |x|) ^ 2 + y ^ 2))) * (2 * π / 3) * |σ - 1| / |σ + 1| ^ 3 := by ring
  unfold leftSlitDensity
  linarith

private lemma leftSlitDensity_upper {x y σ : ℝ} (hy : 0 < y) (hσ : 1 < σ) :
    leftSlitDensity x y σ ≤ (12 / y) * |σ + 1| ^ 3 / (|σ - 1| * |σ - sigmaPlus|) := by
  have hsp1_pos : 0 < σ + 1 := by linarith
  have hsm1_pos : 0 < σ - 1 := sub_pos.mpr hσ
  have hP1 := poissonKernel_le_inv_pi_mul_y (x := x) hy σ
  have hP2 := poissonKernel_le_inv_pi_mul_y (x := x) hy (leftSlitInv σ)
  have hJ1 : invJacobian σ ≤ 4 * π * σ * (σ - 1) / |σ - sigmaPlus| := by
    by_cases hp : σ = sigmaPlus
    · subst hp; unfold invJacobian; simp
    · unfold invJacobian
      have hstar : 0 < σ - sigmaStar := by linarith [sigmaStar_neg]
      rw [abs_of_pos (mul_pos (by linarith) (by nlinarith)), abs_of_pos hstar,
        show σ ^ 2 - 1 = (σ - 1) * (σ + 1) by ring]
      have h1 : σ + 1 ≤ 2 * σ := by linarith
      have h2 : σ / (σ - sigmaStar) ≤ 1 := (div_le_one hstar).mpr (by linarith [sigmaStar_neg])
      have hp_pos : 0 < |σ - sigmaPlus| := abs_pos.mpr (sub_ne_zero.mpr hp)
      calc 2 * π * (σ * ((σ - 1) * (σ + 1))) / ((σ - sigmaStar) * |σ - sigmaPlus|)
          = (σ / (σ - sigmaStar)) * (2 * π * (σ - 1) * (σ + 1) / |σ - sigmaPlus|) := by
            field_simp [hstar.ne', hp_pos.ne']
        _ ≤ 1 * (2 * π * (σ - 1) * (2 * σ) / |σ - sigmaPlus|) := by gcongr
        _ = 4 * π * σ * (σ - 1) / |σ - sigmaPlus| := by ring
  have hJ2 : invJacobian (leftSlitInv σ) ≤ 8 * π * σ / ((σ - 1) * |σ - sigmaPlus|) := by
    rw [invJacobian_leftSlitInv hσ]
    by_cases hp : σ = sigmaPlus
    · subst hp; unfold invJacobian; simp
    · calc (2 / (σ - 1) ^ 2) * invJacobian σ
          ≤ (2 / (σ - 1) ^ 2) * (4 * π * σ * (σ - 1) / |σ - sigmaPlus|) := by gcongr
        _ = 8 * π * σ / ((σ - 1) * |σ - sigmaPlus|) := by
            field_simp [hsm1_pos.ne']; ring
  have hσ_le : σ ≤ |σ + 1| := by rw [abs_of_pos hsp1_pos]; linarith
  have hsm1_le : |σ - 1| ≤ |σ + 1| := by rw [abs_of_pos hsm1_pos, abs_of_pos hsp1_pos]; linarith
  have h1_le : 1 ≤ |σ + 1| := by rw [abs_of_pos hsp1_pos]; linarith
  have hterm1 : poissonKernel x y σ * invJacobian σ ≤
      (4 / y) * |σ + 1| ^ 3 / (|σ - 1| * |σ - sigmaPlus|) := by
    by_cases hp : σ = sigmaPlus
    · subst hp; unfold invJacobian; simp
    · have hp_pos : 0 < |σ - sigmaPlus| := abs_pos.mpr (sub_ne_zero.mpr hp)
      have h1 : poissonKernel x y σ * invJacobian σ ≤
          (1 / (π * y)) * (4 * π * σ * (σ - 1) / |σ - sigmaPlus|) :=
        mul_le_mul hP1 hJ1 (invJacobian_nonneg' _) (by positivity)
      have h2 : (1 / (π * y)) * (4 * π * σ * (σ - 1) / |σ - sigmaPlus|) =
          (4 / y) * σ * |σ - 1| ^ 2 / (|σ - 1| * |σ - sigmaPlus|) := by
        rw [abs_of_pos hsm1_pos]
        field_simp [Real.pi_pos.ne', hy.ne', hsm1_pos.ne', hp_pos.ne']
      have h3 : (4 / y) * σ * |σ - 1| ^ 2 ≤ (4 / y) * |σ + 1| ^ 3 := by
        have : σ * |σ - 1| ^ 2 ≤ |σ + 1| * |σ + 1| ^ 2 :=
          mul_le_mul hσ_le (pow_le_pow_left₀ (abs_nonneg _) hsm1_le 2) (sq_nonneg _) (abs_nonneg _)
        linarith [show |σ + 1| * |σ + 1| ^ 2 = |σ + 1| ^ 3 by ring,
          mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 4 / y)]
      calc poissonKernel x y σ * invJacobian σ
          ≤ (4 / y) * σ * |σ - 1| ^ 2 / (|σ - 1| * |σ - sigmaPlus|) := h1.trans_eq h2
        _ ≤ (4 / y) * |σ + 1| ^ 3 / (|σ - 1| * |σ - sigmaPlus|) := by gcongr
  have hterm2 : poissonKernel x y (leftSlitInv σ) * invJacobian (leftSlitInv σ) ≤
      (8 / y) * |σ + 1| ^ 3 / (|σ - 1| * |σ - sigmaPlus|) := by
    by_cases hp : σ = sigmaPlus
    · subst hp; rw [leftSlitInv_sigmaPlus]; unfold invJacobian; simp
    · have hp_pos : 0 < |σ - sigmaPlus| := abs_pos.mpr (sub_ne_zero.mpr hp)
      have h1 : poissonKernel x y (leftSlitInv σ) * invJacobian (leftSlitInv σ) ≤
          (1 / (π * y)) * (8 * π * σ / ((σ - 1) * |σ - sigmaPlus|)) :=
        mul_le_mul hP2 hJ2 (invJacobian_nonneg' _) (by positivity)
      have h2 : (1 / (π * y)) * (8 * π * σ / ((σ - 1) * |σ - sigmaPlus|)) =
          (8 / y) * σ / (|σ - 1| * |σ - sigmaPlus|) := by
        rw [abs_of_pos hsm1_pos]
        field_simp [Real.pi_pos.ne', hy.ne', hsm1_pos.ne', hp_pos.ne']
      have h3 : (8 / y) * σ ≤ (8 / y) * |σ + 1| ^ 3 := by
        have : σ ≤ |σ + 1| ^ 3 := by
          calc σ ≤ |σ + 1| := hσ_le
            _ = |σ + 1| * 1 ^ 2 := by ring
            _ ≤ |σ + 1| * |σ + 1| ^ 2 := mul_le_mul_of_nonneg_left
                (pow_le_pow_left₀ zero_le_one h1_le 2) (abs_nonneg _)
            _ = |σ + 1| ^ 3 := by ring
        gcongr
      calc poissonKernel x y (leftSlitInv σ) * invJacobian (leftSlitInv σ)
          ≤ (8 / y) * σ / (|σ - 1| * |σ - sigmaPlus|) := h1.trans_eq h2
        _ ≤ (8 / y) * |σ + 1| ^ 3 / (|σ - 1| * |σ - sigmaPlus|) := by gcongr
  unfold leftSlitDensity
  calc poissonKernel x y σ * invJacobian σ +
        poissonKernel x y (leftSlitInv σ) * invJacobian (leftSlitInv σ)
      ≤ (4 / y) * |σ + 1| ^ 3 / (|σ - 1| * |σ - sigmaPlus|) +
          (8 / y) * |σ + 1| ^ 3 / (|σ - 1| * |σ - sigmaPlus|) := add_le_add hterm1 hterm2
    _ = (12 / y) * |σ + 1| ^ 3 / (|σ - 1| * |σ - sigmaPlus|) := by ring

private lemma poissonKernel_le_bracket' {x y : ℝ} (hy : 0 < y) (u : ℝ) :
    poissonKernel x y u ≤ (y * ((1 + 2 * x ^ 2) / y ^ 2 + 2) / π) * (1 + u ^ 2)⁻¹ := by
  unfold poissonKernel
  have hD : 0 < (u - x) ^ 2 + y ^ 2 := by positivity
  have hpi := Real.pi_pos
  have hM : 1 + u ^ 2 ≤ ((1 + 2 * x ^ 2) / y ^ 2 + 2) * ((u - x) ^ 2 + y ^ 2) := by
    have h1 : 1 + 2 * x ^ 2 ≤ (1 + 2 * x ^ 2) / y ^ 2 * ((u - x) ^ 2 + y ^ 2) := by
      calc 1 + 2 * x ^ 2 = (1 + 2 * x ^ 2) / y ^ 2 * y ^ 2 := by field_simp
        _ ≤ _ := by gcongr; nlinarith [sq_nonneg (u - x)]
    nlinarith [sq_nonneg (u - 2 * x), sq_nonneg (u - x)]
  rw [div_le_iff₀ (by positivity)]
  have hcalc : (y * ((1 + 2 * x ^ 2) / y ^ 2 + 2) / π * (1 + u ^ 2)⁻¹) *
      (π * ((u - x) ^ 2 + y ^ 2)) =
      y * (((1 + 2 * x ^ 2) / y ^ 2 + 2) * ((u - x) ^ 2 + y ^ 2)) / (1 + u ^ 2) := by
    field_simp
  rw [hcalc, le_div_iff₀ (by positivity)]
  nlinarith

private lemma integrable_abs_log_mul_poisson' (x : ℝ) {y : ℝ} (hy : 0 < y) :
    Integrable (fun u : ℝ => |Real.log (|u|)| * poissonKernel x y u) := by
  set C₀ : ℝ := y * ((1 + 2 * x ^ 2) / y ^ 2 + 2) / π
  have hmeas : AEStronglyMeasurable (fun u : ℝ => |Real.log (|u|)| * poissonKernel x y u) volume :=
    ((continuous_poissonKernel x hy).measurable.mul
      (Real.measurable_log.comp measurable_abs).abs).aestronglyMeasurable.congr
      (Eventually.of_forall fun u => mul_comm _ _)
  have hbr : Integrable (fun u : ℝ => (1 + ‖u‖ ^ 2) ^ (-(3 / 2 : ℝ) / 2)) := by
    refine integrable_rpow_neg_one_add_norm_sq (E := ℝ) (r := 3 / 2) ?_
    simp; norm_num
  have hK : IntegrableOn (fun u : ℝ => |Real.log (|u|)| * poissonKernel x y u) (Icc (-1) 1) := by
    have hlog : IntervalIntegrable (fun u : ℝ => |Real.log (|u|)|) volume (-1) 1 := by
      have := (intervalIntegral.intervalIntegrable_log' (a := -1) (b := 1)).abs
      have e : (fun u : ℝ => |Real.log (|u|)|) = fun u => |Real.log u| := by
        funext u; rw [Real.log_abs]
      rw [e]; exact this
    have h2 : IntegrableOn (fun u : ℝ => |Real.log (|u|)|) (Icc (-1) 1) := by
      rw [integrableOn_Icc_iff_integrableOn_Ioc]
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp hlog
    exact h2.mul_continuousOn (continuous_poissonKernel x hy).continuousOn isCompact_Icc
  have hT : IntegrableOn (fun u : ℝ => |Real.log (|u|)| * poissonKernel x y u) (Icc (-1) 1)ᶜ := by
    refine Integrable.mono' (g := fun u => 2 * C₀ * (1 + ‖u‖ ^ 2) ^ (-(3 / 2 : ℝ) / 2))
      (hbr.const_mul (2 * C₀)).integrableOn hmeas.restrict ?_
    refine (ae_restrict_iff' isClosed_Icc.measurableSet.compl).mpr (Eventually.of_forall fun u hu => ?_)
    have hu1 : 1 ≤ |u| := by
      simp only [mem_compl_iff, mem_Icc, not_and_or, not_le] at hu
      rcases hu with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    have hpos : 0 < 1 + u ^ 2 := by positivity
    have hlog : |Real.log (|u|)| ≤ 2 * (1 + u ^ 2) ^ (1 / 4 : ℝ) := by
      rw [abs_of_nonneg (Real.log_nonneg hu1)]
      have h1 : Real.log |u| = Real.log (u ^ 2) / 2 := by
        rw [← sq_abs u, Real.log_pow]; push_cast; ring
      have h2 := Real.log_le_rpow_div (x := u ^ 2) (sq_nonneg u) (by norm_num : (0 : ℝ) < 1 / 4)
      have h3 : (u ^ 2) ^ (1 / 4 : ℝ) ≤ (1 + u ^ 2) ^ (1 / 4 : ℝ) :=
        Real.rpow_le_rpow (sq_nonneg u) (by linarith) (by norm_num)
      rw [h1]
      have : Real.log (u ^ 2) ≤ 4 * (1 + u ^ 2) ^ (1 / 4 : ℝ) := by
        calc Real.log (u ^ 2) ≤ (u ^ 2) ^ (1 / 4 : ℝ) / (1 / 4) := h2
          _ = 4 * (u ^ 2) ^ (1 / 4 : ℝ) := by ring
          _ ≤ 4 * (1 + u ^ 2) ^ (1 / 4 : ℝ) := by gcongr
      linarith
    have hP := poissonKernel_le_bracket' (x := x) hy u
    have hP0 := poissonKernel_nonneg (x := x) hy.le u
    rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) hP0), Real.norm_eq_abs, sq_abs]
    calc |Real.log (|u|)| * poissonKernel x y u
        ≤ (2 * (1 + u ^ 2) ^ (1 / 4 : ℝ)) * (C₀ * (1 + u ^ 2)⁻¹) :=
          mul_le_mul hlog hP hP0 (by positivity)
      _ = 2 * C₀ * (1 + u ^ 2) ^ (-(3 / 2 : ℝ) / 2) := by
          rw [show (-(3 / 2 : ℝ) / 2) = 1 / 4 + (-1) by norm_num, Real.rpow_add hpos,
            Real.rpow_neg_one]
          ring
  have := hK.union hT
  rwa [union_compl_self, integrableOn_univ] at this

lemma integrable_abs_log_sub_mul_poissonKernel (a x : ℝ) {y : ℝ} (hy : 0 < y) :
    Integrable (fun σ : ℝ => |Real.log (|σ - a|)| * poissonKernel x y σ) := by
  have hi := (integrable_abs_log_mul_poisson' (x - a) hy).comp_sub_right a
  refine hi.congr (Eventually.of_forall fun σ => ?_)
  unfold poissonKernel; congr 3; ring

theorem integrableOn_poisson_mul_log_slitDensity (x : ℝ) {y : ℝ} (hy : 0 < y) :
    IntegrableOn (fun σ : ℝ => poissonKernel x y σ * Real.log (slitDensity x y σ)) slitPreimage := by
  have hi0 := integrable_abs_log_sub_mul_poissonKernel 0 x hy
  have him1 := integrable_abs_log_sub_mul_poissonKernel (-1) x hy
  have hi1 := integrable_abs_log_sub_mul_poissonKernel 1 x hy
  have histar := integrable_abs_log_sub_mul_poissonKernel sigmaStar x hy
  have hiplus := integrable_abs_log_sub_mul_poissonKernel sigmaPlus x hy
  have hP := integrable_poissonKernel x hy
  have hmeas : Measurable (fun σ : ℝ => poissonKernel x y σ * Real.log (slitDensity x y σ)) := by
    have h1 : Measurable (rightSlitDensity x y) := by
      unfold rightSlitDensity poissonKernel slitInv invJacobian; fun_prop
    have h2 : Measurable (leftSlitDensity x y) := by
      unfold leftSlitDensity poissonKernel leftSlitInv invJacobian; fun_prop
    have hs : Measurable (slitDensity x y) := Measurable.ite measurableSet_Iio h1 h2
    exact (continuous_poissonKernel x hy).measurable.mul (Real.measurable_log.comp hs)
  have hIoo : IntegrableOn (fun σ : ℝ => poissonKernel x y σ * Real.log (slitDensity x y σ)) (Ioo (-1) 0) := by
    let cR : ℝ := (y / (π * ((|x| + 1) ^ 2 + y ^ 2))) * (π / 4)
    let CR : ℝ := 2.61 * (1 + √2) / (π * y)
    have hcR : 0 < cR := by dsimp [cR]; positivity
    have hCR : 0 < CR := by dsimp [CR]; positivity
    let C₀ : ℝ := |Real.log cR| + |Real.log CR|
    let dom : ℝ → ℝ := fun σ =>
      C₀ * poissonKernel x y σ + |Real.log (|σ - 0|)| * poissonKernel x y σ +
        |Real.log (|σ - (-1)|)| * poissonKernel x y σ + |Real.log (|σ - sigmaStar|)| * poissonKernel x y σ
    have hdom_int : Integrable dom :=
      (((hP.const_mul C₀).add hi0).add him1).add histar
    refine hdom_int.integrableOn.mono' hmeas.aestronglyMeasurable ?_
    have hnull : volume ({sigmaStar} : Set ℝ) = 0 := ({sigmaStar} : Set ℝ).toFinite.measure_zero volume
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [compl_mem_ae_iff.mpr hnull] with σ hne hσ
    have hne' : σ ≠ sigmaStar := by simpa using hne
    have hlo : cR * |σ| * |σ + 1| ≤ rightSlitDensity x y σ := rightSlitDensity_lower (x := x) hy hσ hne'
    have hhi : rightSlitDensity x y σ ≤ CR / |σ - sigmaStar| := rightSlitDensity_upper' (x := x) hy hσ
    have h0 : σ ≠ 0 := hσ.2.ne
    have hm1 : σ + 1 ≠ 0 := by linarith [hσ.1]
    have ha_pos : 0 < cR * |σ| * |σ + 1| := by positivity
    have habs_log := abs_log_le_max_of_bounds ha_pos hlo hhi
    have hlog_a : |Real.log (cR * |σ| * |σ + 1|)| ≤
        |Real.log cR| + |Real.log (|σ|)| + |Real.log (|σ + 1|)| := by
      rw [Real.log_mul (mul_ne_zero hcR.ne' (abs_ne_zero.mpr h0)) (abs_ne_zero.mpr hm1),
        Real.log_mul hcR.ne' (abs_ne_zero.mpr h0)]
      linarith [abs_add_le (Real.log cR + Real.log (|σ|)) (Real.log (|σ + 1|)),
        abs_add_le (Real.log cR) (Real.log (|σ|))]
    have hlog_b : |Real.log (CR / |σ - sigmaStar|)| ≤ |Real.log CR| + |Real.log (|σ - sigmaStar|)| := by
      rw [Real.log_div hCR.ne' (abs_ne_zero.mpr (sub_ne_zero.mpr hne'))]
      exact abs_sub _ _
    have hP0 := poissonKernel_nonneg (x := x) hy.le σ
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hP0, slitDensity, if_pos hσ.2]
    dsimp [dom, C₀]
    simp only [sub_zero, sub_neg_eq_add]
    have hsum_log : |Real.log (rightSlitDensity x y σ)| ≤
        C₀ + |Real.log (|σ|)| + |Real.log (|σ + 1|)| + |Real.log (|σ - sigmaStar|)| := by
      dsimp [C₀]; linarith
    calc poissonKernel x y σ * |Real.log (rightSlitDensity x y σ)|
        ≤ poissonKernel x y σ * (C₀ + |Real.log (|σ|)| + |Real.log (|σ + 1|)| + |Real.log (|σ - sigmaStar|)|) := by
          gcongr
      _ = _ := by ring
  have hIoi : IntegrableOn (fun σ : ℝ => poissonKernel x y σ * Real.log (slitDensity x y σ)) (Ioi 1) := by
    let cL : ℝ := (y / (π * ((1 + |x|) ^ 2 + y ^ 2))) * (2 * π / 3)
    let CL : ℝ := 12 / y
    have hcL : 0 < cL := by dsimp [cL]; positivity
    have hCL : 0 < CL := by dsimp [CL]; positivity
    let C₁ : ℝ := |Real.log cL| + |Real.log CL|
    let dom : ℝ → ℝ := fun σ =>
      C₁ * poissonKernel x y σ + 2 * (|Real.log (|σ - 1|)| * poissonKernel x y σ) +
        6 * (|Real.log (|σ - (-1)|)| * poissonKernel x y σ) + |Real.log (|σ - sigmaPlus|)| * poissonKernel x y σ
    have hdom_int : Integrable dom :=
      (((hP.const_mul C₁).add (hi1.const_mul 2)).add (him1.const_mul 6)).add hiplus
    refine hdom_int.integrableOn.mono' hmeas.aestronglyMeasurable ?_
    have hnull : volume ({sigmaPlus} : Set ℝ) = 0 := ({sigmaPlus} : Set ℝ).toFinite.measure_zero volume
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards [compl_mem_ae_iff.mpr hnull] with σ hne hσ
    have hne' : σ ≠ sigmaPlus := by simpa using hne
    have hgt1 : 1 < σ := hσ
    have hlo : cL * |σ - 1| / |σ + 1| ^ 3 ≤ leftSlitDensity x y σ := leftSlitDensity_lower (x := x) hy hgt1 hne'
    have hhi : leftSlitDensity x y σ ≤ CL * |σ + 1| ^ 3 / (|σ - 1| * |σ - sigmaPlus|) :=
      leftSlitDensity_upper (x := x) hy hgt1
    have hm1_ne : σ - 1 ≠ 0 := sub_ne_zero.mpr hgt1.ne'
    have hp1_ne : σ + 1 ≠ 0 := by linarith
    have hp_ne : |σ - sigmaPlus| ≠ 0 := abs_ne_zero.mpr (sub_ne_zero.mpr hne')
    have ha_pos : 0 < cL * |σ - 1| / |σ + 1| ^ 3 := by positivity
    have habs_log := abs_log_le_max_of_bounds ha_pos hlo hhi
    have hab3 : |3 * Real.log (|σ + 1|)| = 3 * |Real.log (|σ + 1|)| := by
      rw [abs_mul, abs_of_pos (by norm_num)]
    have hlog_a : |Real.log (cL * |σ - 1| / |σ + 1| ^ 3)| ≤
        |Real.log cL| + |Real.log (|σ - 1|)| + 3 * |Real.log (|σ + 1|)| := by
      rw [Real.log_div (mul_ne_zero hcL.ne' (abs_ne_zero.mpr hm1_ne)) (pow_ne_zero 3 (abs_ne_zero.mpr hp1_ne)),
        Real.log_mul hcL.ne' (abs_ne_zero.mpr hm1_ne), Real.log_pow, Nat.cast_ofNat]
      linarith [abs_sub (Real.log cL + Real.log (|σ - 1|)) (3 * Real.log (|σ + 1|)),
        abs_add_le (Real.log cL) (Real.log (|σ - 1|)), hab3]
    have hlog_b : |Real.log (CL * |σ + 1| ^ 3 / (|σ - 1| * |σ - sigmaPlus|))| ≤
        |Real.log CL| + 3 * |Real.log (|σ + 1|)| + |Real.log (|σ - 1|)| + |Real.log (|σ - sigmaPlus|)| := by
      rw [Real.log_div (mul_ne_zero hCL.ne' (pow_ne_zero 3 (abs_ne_zero.mpr hp1_ne)))
          (mul_ne_zero (abs_ne_zero.mpr hm1_ne) hp_ne),
        Real.log_mul hCL.ne' (pow_ne_zero 3 (abs_ne_zero.mpr hp1_ne)),
        Real.log_mul (abs_ne_zero.mpr hm1_ne) hp_ne, Real.log_pow, Nat.cast_ofNat]
      linarith [abs_sub (Real.log CL + 3 * Real.log (|σ + 1|)) (Real.log (|σ - 1|) + Real.log (|σ - sigmaPlus|)),
        abs_add_le (Real.log CL) (3 * Real.log (|σ + 1|)),
        abs_add_le (Real.log (|σ - 1|)) (Real.log (|σ - sigmaPlus|)), hab3]
    have hP0 := poissonKernel_nonneg (x := x) hy.le σ
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hP0, slitDensity, if_neg (by linarith)]
    dsimp [dom, C₁]
    simp only [sub_neg_eq_add]
    have hsum_log : |Real.log (leftSlitDensity x y σ)| ≤
        C₁ + 2 * |Real.log (|σ - 1|)| + 6 * |Real.log (|σ + 1|)| + |Real.log (|σ - sigmaPlus|)| := by
      dsimp [C₁]; linarith
    calc poissonKernel x y σ * |Real.log (leftSlitDensity x y σ)|
        ≤ poissonKernel x y σ *
            (C₁ + 2 * |Real.log (|σ - 1|)| + 6 * |Real.log (|σ + 1|)| + |Real.log (|σ - sigmaPlus|)|) := by
          gcongr
      _ = _ := by ring
  exact hIoo.union hIoi

theorem setIntegral_poisson_mul_log_slitDensity_le_entropy (x : ℝ) {y : ℝ} (hy : 0 < y) :
    ∫ σ in slitPreimage, poissonKernel x y σ * Real.log (slitDensity x y σ) ≤
      slitEntropy x y := by
  have hint_log := integrableOn_poisson_mul_log_slitDensity x hy
  have h1 : Measurable (rightSlitDensity x y) := by
    unfold rightSlitDensity poissonKernel slitInv invJacobian; fun_prop
  have h2 : Measurable (leftSlitDensity x y) := by
    unfold leftSlitDensity poissonKernel leftSlitInv invJacobian; fun_prop
  have hs : Measurable (slitDensity x y) := Measurable.ite measurableSet_Iio h1 h2
  let g : ℝ → ℝ := fun σ => poissonKernel x y σ * max 0 (Real.log (slitDensity x y σ))
  have hmeas_g : AEStronglyMeasurable g (volume.restrict slitPreimage) :=
    ((continuous_poissonKernel x hy).measurable.mul
      (Measurable.max measurable_const (Real.measurable_log.comp hs))).aestronglyMeasurable
  have hg_all : IntegrableOn g slitPreimage := by
    refine Integrable.mono hint_log hmeas_g (Eventually.of_forall fun σ => ?_)
    dsimp [g]
    have hP0 := poissonKernel_nonneg (x := x) hy.le σ
    simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hP0]
    refine mul_le_mul_of_nonneg_left ?_ hP0
    exact abs_le.mpr ⟨by linarith [le_max_left 0 (Real.log (slitDensity x y σ)), abs_nonneg (Real.log (slitDensity x y σ))],
      max_le (abs_nonneg _) (le_abs_self _)⟩
  have hmono := setIntegral_mono_on hint_log hg_all (measurableSet_Ioo.union measurableSet_Ioi)
    fun σ _ => mul_le_mul_of_nonneg_left (le_max_right 0 _) (poissonKernel_nonneg hy.le σ)
  refine hmono.trans_eq ?_
  have hg_Ioo : IntegrableOn g (Ioo (-1) 0) := hg_all.mono_set Set.subset_union_left
  have hg_Ioi : IntegrableOn g (Ioi 1) := hg_all.mono_set Set.subset_union_right
  have hdisj : Disjoint (Ioo (-1 : ℝ) 0) (Ioi 1) := by
    rw [Set.disjoint_left]; intro σ h1 h2; linarith [h1.2, show 1 < σ from h2]
  unfold slitPreimage slitEntropy rightSlitEntropy leftSlitEntropy
  rw [setIntegral_union hdisj measurableSet_Ioi hg_Ioo hg_Ioi]
  congr 1
  · refine setIntegral_congr_fun measurableSet_Ioo fun σ hσ => ?_
    dsimp [g]; unfold slitDensity; rw [if_pos hσ.2]
  · refine setIntegral_congr_fun measurableSet_Ioi fun σ hσ => ?_
    dsimp [g]; unfold slitDensity; rw [if_neg (by linarith [show 1 < σ from hσ])]

/-- info: 'FormalResearch.ModularBootstrap.PoissonJensen.hankelContinuation_bdy_ne_zero_ae' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.PoissonJensen.hankelContinuation_bdy_ne_zero_ae

/-- info: 'FormalResearch.ModularBootstrap.PoissonJensen.eSlitMass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.PoissonJensen.eSlitMass

/-- info: 'FormalResearch.ModularBootstrap.PoissonJensen.setIntegral_slitPreimage_div_slitDensity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.PoissonJensen.setIntegral_slitPreimage_div_slitDensity

/-- info: 'FormalResearch.ModularBootstrap.PoissonJensen.integrableOn_poisson_mul_log_slitDensity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.PoissonJensen.integrableOn_poisson_mul_log_slitDensity

/-- info: 'FormalResearch.ModularBootstrap.PoissonJensen.setIntegral_poisson_mul_log_slitDensity_le_entropy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.PoissonJensen.setIntegral_poisson_mul_log_slitDensity_le_entropy

end FormalResearch.ModularBootstrap.PoissonJensen
