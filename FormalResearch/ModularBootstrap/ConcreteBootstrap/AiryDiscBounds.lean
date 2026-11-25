module

public import FormalResearch.ModularBootstrap.ConcreteBootstrap.LemmaQ
public import FormalResearch.ModularBootstrap.ConcreteBootstrap.ClarkDiscBounds
public import FormalResearch.Special.AiryCft2Ball
public import FormalResearch.Special.AiryCftQuadrature
public import FormalResearch.Special.AiryCftSignUncertainty
public import FormalResearch.Special.AiryAsymNeg
public import Mathlib.Analysis.Complex.Liouville

/-!
# Subharmonic Disc Averaging, Circle `L¹` Bounds, and Split Airy Defect Formula

Shared analytic infrastructure for `QuantC1Airy` (`Proposition TE.0` at `α = 0`, type `(II)`)
and `BootstrapHB` (`Theorem FT-L.FW` at `(P, Q) = (1, 0)`):

* `airy_defect_ball_split`: split form of `airy_defect_ball` over `θ ∈ (-π, π)` bounding the
  quadrature defect by `(15 * √π * R) * ∫_{-π}^{π} B(θ) dθ` for any integrable majorant `B` of
  `‖f(R e^{iθ})‖ / airyEnv(R e^{iθ})`.
* `typeII_disc_avg_bound`: Step 0 subharmonic disc averaging (`subharmonic_disc_avg_le` +
  `disc_avg_neg_log_tipDist` + `tipH_disc_oscillation`) converting a slit type-(II) envelope into
  a cut-inclusive pointwise bound `‖Ψ u₀‖ ≤ C exp(ς √(R₁+2)) airyEnv u₀ min((1+‖u₀‖)^{1/2}, |Im u₀|⁻¹)`.
* `typeII_cut_bound`, `typeII_deriv_bound`, `typeII_deriv2_bound`: Cauchy bounds on `closedBall 0 R₁`.
* `typeII_circle_env_integral`: `r`-independent `L¹` circle bound `∫_{-π}^π ‖Ψ(r e^{iθ})‖ / e ≤ C_circ`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real

namespace FormalResearch.ModularBootstrap.ConcreteBootstrap

open FormalResearch.Special

/-! ### Section 1: Split circle-integral form of `airy_defect_ball` -/

lemma airy_volume_real_axis_zero : volume {u : ℂ | u.im = 0} = 0 := by
  let L : ℂ →ₗ[ℝ] ℝ :=
    { toFun := fun u => u.im
      map_add' := fun a b => Complex.add_im a b
      map_smul' := fun r a => by simp }
  have hne : LinearMap.ker L ≠ ⊤ := by
    intro htop
    have hI : (I : ℂ) ∈ LinearMap.ker L := htop ▸ Submodule.mem_top
    have h0 : (I : ℂ).im = 0 := by simpa [L, LinearMap.mem_ker] using hI
    simp at h0
  have hsub : {u : ℂ | u.im = 0} = (LinearMap.ker L : Set ℂ) := by
    ext u; simp [L, LinearMap.mem_ker]
  rw [hsub]
  exact MeasureTheory.Measure.addHaar_submodule volume (LinearMap.ker L) hne

lemma ball_zero_set_measure_zero {f : ℂ → ℂ} {u₀ : ℂ} {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hf : AnalyticOnNhd ℂ f (ball u₀ R)) (hf0 : f u₀ ≠ 0) :
    volume {u ∈ ball u₀ r | f u = 0} = 0 := by
  classical
  have hnot_zero : ¬ EqOn f 0 (ball u₀ R) := fun h => hf0 (h (mem_ball_self (hr.trans hrR)))
  have hev : ∀ z ∈ ball u₀ R, ∀ᶠ w in 𝓝[≠] z, f w ≠ 0 := by
    rcases hf.eqOn_zero_or_eventually_ne_zero_of_preconnected (convex_ball u₀ R).isPreconnected with
      h | h
    · exact absurd h hnot_zero
    · intro z hz
      have h1 := mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp h z hz
      have h2 : ball u₀ R ∈ 𝓝[≠] z := nhdsWithin_le_nhds (isOpen_ball.mem_nhds hz)
      filter_upwards [h1, h2] with w hw1 hw2
      rcases hw1 with hw | hw
      · exact hw
      · exact absurd hw2 hw
  have hopen : ∀ z ∈ closedBall u₀ r, ∃ δ > 0, ∀ w ∈ ball z δ, w ≠ z → f w ≠ 0 := fun z hz => by
    have hzR : z ∈ ball u₀ R := closedBall_subset_ball hrR hz
    obtain ⟨U, hU, hUf⟩ := (hev z hzR).exists_mem
    rw [mem_nhdsWithin] at hU
    obtain ⟨V, hV_open, hzV, hVU⟩ := hU
    obtain ⟨δ, hδ_pos, hδ_sub⟩ := Metric.isOpen_iff.mp hV_open z hzV
    exact ⟨δ, hδ_pos, fun w hw hwz => hUf w (hVU ⟨hδ_sub hw, hwz⟩)⟩
  choose δ hδ_pos hδ_ne using hopen
  obtain ⟨s, hs⟩ := (isCompact_closedBall u₀ r).elim_nhds_subcover
    (fun z => if hz : z ∈ closedBall u₀ r then ball z (δ z hz) else ∅)
    fun z hz => by simp only [hz, ↓reduceDIte]; exact ball_mem_nhds z (hδ_pos z hz)
  have hsub : {u ∈ ball u₀ r | f u = 0} ⊆ (s : Set ℂ) := by
    intro u ⟨hu_ball, hu_f0⟩
    have hu_cl : u ∈ closedBall u₀ r := ball_subset_closedBall hu_ball
    obtain ⟨z, hzs, hu_in⟩ := mem_iUnion₂.mp (hs.2 hu_cl)
    have hz_cl : z ∈ closedBall u₀ r := hs.1 z hzs
    simp only [hz_cl, ↓reduceDIte] at hu_in
    by_contra hne
    exact absurd hu_f0 (hδ_ne z hz_cl u hu_in fun h_eq => hne (h_eq ▸ hzs))
  exact measure_mono_null hsub (s.finite_toSet.measure_zero volume)

/-- **Integral-split Airy defect bound** on a good circle `‖w‖ = R`:
for `f` holomorphic on `ball 0 R'` (`R < R'`), if `‖f (circleMap 0 R θ)‖ / airyEnv (circleMap 0 R θ) ≤ B θ`
on `[-π, π]`, then the quadrature defect is bounded by `(15 * √π * R) * ∫_{-π}^{π} B θ dθ`. -/
theorem airy_defect_ball_split {N : ℕ} {R R' : ℝ}
    (hD : CftCircleData airyAiC (fun n => (airyZero n : ℂ)) (Finset.Icc 1 N) R)
    (hRR : R < R') {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball 0 R'))
    (hRp : ∀ w : ℂ, ‖w‖ = R → 0 ≤ w.im →
      ‖(airyBiC w - I * airyAiC w) / airyAiC w‖ * airyEnv w ≤ 30 * √π)
    (hRm : ∀ w : ℂ, ‖w‖ = R → w.im ≤ 0 →
      ‖(airyBiC w + I * airyAiC w) / airyAiC w‖ * airyEnv w ≤ 30 * √π)
    {B : ℝ → ℝ} (hB_int : IntervalIntegrable B volume (-π) π)
    (hB_bd : ∀ θ ∈ Icc (-π) π,
      ‖f (circleMap 0 R θ)‖ / airyEnv (circleMap 0 R θ) ≤ B θ) :
    ‖(∑ n ∈ Finset.Icc 1 N, f (airyZero n : ℂ) / (deriv airyAiC (airyZero n : ℂ)) ^ 2) -
        ∫ x in (-R)..R, f (x : ℂ)‖ ≤
      (15 * √π * R) * ∫ θ in (-π)..π, B θ := by
  have h := cft2_defect_ball_split hD differentiable_airyBiC hRR hf airyEnv_pos
    (fun w hw him => by
      have hA := hD.ne_zero_sphere hw
      have e : airyBiC w / airyAiC w - I = (airyBiC w - I * airyAiC w) / airyAiC w := by
        field_simp
      rw [e]; exact hRp w hw him)
    (fun w hw him => by
      have hA := hD.ne_zero_sphere hw
      have e : airyBiC w / airyAiC w + I = (airyBiC w + I * airyAiC w) / airyAiC w := by
        field_simp
      rw [e]; exact hRm w hw him)
    hB_int hB_bd
  have hsum : (-(π : ℂ)) * (∑ n ∈ Finset.Icc 1 N, f (airyZero n : ℂ) * airyBiC (airyZero n : ℂ) /
      deriv airyAiC (airyZero n : ℂ)) =
      ∑ n ∈ Finset.Icc 1 N, f (airyZero n : ℂ) / (deriv airyAiC (airyZero n : ℂ)) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [cftDef_airyBiC_at_zero n]
    have hd := airyZero_deriv_ne_zero n
    have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp
  rw [hsum, show 30 * √π / 2 * R = 15 * √π * R by ring] at h
  exact h



/-! ### Section 2: Subharmonic disc averaging for type `(II)` Airy envelopes -/

private lemma typeII_exponent_oscillation {u₀ u : ℂ}
    (hu : u ∈ ball u₀ ((1 / 2 : ℝ) * (1 + ‖u₀‖) ^ (-(1 / 2 : ℝ)))) :
    |(-(4 / 3 : ℝ) * (u ^ (3 / 2 : ℂ)).re) - (-(4 / 3 : ℝ) * (u₀ ^ (3 / 2 : ℂ)).re)| ≤ 1 := by
  have hball_neg : -u ∈ ball (-u₀) ((1 / 2 : ℝ) * (1 + ‖-u₀‖) ^ (-(1 / 2 : ℝ))) := by
    rw [mem_ball, dist_eq_norm] at hu ⊢
    rwa [norm_neg, show -u - -u₀ = -(u - u₀) by ring, norm_neg]
  have hosc := tipH_disc_oscillation (-u₀) (-u) hball_neg
  have hH_eq : ∀ z : ℂ, tipH (-z) = -(4 / 3 : ℝ) * betaTip ^ (3 / 2 : ℝ) * (z ^ (3 / 2 : ℂ)).re := by
    intro z
    unfold tipH
    rw [neg_neg, ← four_thirds_betaTip_rpow]
    ring
  rw [hH_eq u, hH_eq u₀] at hosc
  have hb32 : 0 < betaTip ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos betaTip_pos _
  have hfour : (3 * KTip / 4 : ℝ) = betaTip ^ (3 / 2 : ℝ) := by
    linarith [four_thirds_betaTip_rpow]
  rw [hfour] at hosc
  have hfac : -(4 / 3 : ℝ) * betaTip ^ (3 / 2 : ℝ) * (u ^ (3 / 2 : ℂ)).re -
      (-(4 / 3 : ℝ) * betaTip ^ (3 / 2 : ℝ) * (u₀ ^ (3 / 2 : ℂ)).re) =
      betaTip ^ (3 / 2 : ℝ) * ((-(4 / 3 : ℝ) * (u ^ (3 / 2 : ℂ)).re) -
        (-(4 / 3 : ℝ) * (u₀ ^ (3 / 2 : ℂ)).re)) := by ring
  rw [hfac, abs_mul, abs_of_pos hb32] at hosc
  exact (mul_le_iff_le_one_right hb32).mp hosc

/-- **Step 0 disc averaging** for any holomorphic `Ψ` obeying a type-(II) slit envelope on
`closedBall 0 R_dom \ (-∞, 0]`, giving cut-inclusive bounds on `closedBall 0 R₁` (`R₁ + 2 ≤ R_dom`). -/
theorem typeII_disc_avg_bound {Ψ : ℂ → ℂ} {R_dom R₁ C_0 ς : ℝ}
    (_hR₁ : 0 ≤ R₁) (hR_dom : R₁ + 2 ≤ R_dom) (hC0 : 0 < C_0) (hς : 0 ≤ ς)
    (hΨ_an : AnalyticOnNhd ℂ Ψ (closedBall (0 : ℂ) R_dom))
    (hΨ_env : ∀ u ∈ closedBall (0 : ℂ) R_dom, ¬ (u.im = 0 ∧ u.re ≤ 0) →
      ‖Ψ u‖ ≤ C_0 * airyEnv u * Real.exp (ς * (u ^ (1 / 2 : ℂ)).re) *
        ‖u‖ ^ (-(1 / 2 : ℝ)) * ((u ^ (1 / 2 : ℂ)).re)⁻¹)
    {u₀ : ℂ} (hu₀ : u₀ ∈ closedBall (0 : ℂ) R₁) :
    ‖Ψ u₀‖ ≤ 8 * Real.exp (5 / 2) * C_0 * Real.exp (ς * √(R₁ + 2)) *
        airyEnv u₀ * (1 + ‖u₀‖) ^ (1 / 2 : ℝ) ∧
    (2 * ((1 / 2 : ℝ) * (1 + ‖u₀‖) ^ (-(1 / 2 : ℝ))) ≤ |u₀.im| →
      ‖Ψ u₀‖ ≤ 8 * Real.exp (5 / 2) * C_0 * Real.exp (ς * √(R₁ + 2)) *
        airyEnv u₀ * (1 / |u₀.im|)) := by
  let r : ℝ := (1 / 2 : ℝ) * (1 + ‖u₀‖) ^ (-(1 / 2 : ℝ))
  have hr_pos : 0 < r := by positivity
  have hr_le_half : r ≤ 1 / 2 := by
    have : (1 + ‖u₀‖) ^ (-(1 / 2 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg u₀]) (by norm_num)
    dsimp [r]; linarith
  have hu₀_norm : ‖u₀‖ ≤ R₁ := mem_closedBall_zero_iff.mp hu₀
  have hcl_sub : closedBall u₀ r ⊆ closedBall (0 : ℂ) R_dom := fun u hu => by
    rw [mem_closedBall, dist_zero_right]
    rw [mem_closedBall, dist_eq_norm] at hu
    calc ‖u‖ = ‖(u - u₀) + u₀‖ := by ring_nf
      _ ≤ ‖u - u₀‖ + ‖u₀‖ := norm_add_le _ _
      _ ≤ r + R₁ := add_le_add hu hu₀_norm
      _ ≤ R_dom := by linarith
  have hball_big : ball u₀ (r + 1) ⊆ closedBall (0 : ℂ) R_dom := fun u hu => by
    rw [mem_closedBall, dist_zero_right]
    rw [mem_ball, dist_eq_norm] at hu
    calc ‖u‖ = ‖(u - u₀) + u₀‖ := by ring_nf
      _ ≤ ‖u - u₀‖ + ‖u₀‖ := norm_add_le _ _
      _ ≤ (r + 1) + R₁ := add_le_add hu.le hu₀_norm
      _ ≤ R_dom := by linarith
  have havg_full := disc_avg_neg_log_tipDist (-u₀)
  simp only [norm_neg] at havg_full
  have hball_vol : volume.real (ball u₀ r) = π * r ^ 2 := by
    rw [Measure.real_def, Complex.volume_ball, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal hr_pos.le, ENNReal.coe_toReal, NNReal.coe_real_pi]
    ring
  have hneg_mp : MeasurePreserving (fun u : ℂ => -u) volume volume :=
    Measure.measurePreserving_neg volume
  have hneg_int : IntegrableOn (fun u : ℂ => -Real.log (tipDist (-u))) (ball u₀ r) ∧
      ∫ u in ball u₀ r, (-Real.log (tipDist (-u))) =
        ∫ ζ in ball (-u₀) r, (-Real.log (tipDist ζ)) := by
    have hpre : (fun u : ℂ => -u) ⁻¹' ball (-u₀) r = ball u₀ r := by
      ext u; simp [mem_ball, dist_eq_norm]
    have hmap : Measure.map (fun u : ℂ => -u) (volume.restrict (ball u₀ r)) =
        volume.restrict (ball (-u₀) r) := by
      change Measure.map Neg.neg (volume.restrict (ball u₀ r)) = volume.restrict (ball (-u₀) r)
      rw [← hpre]
      rw [← Measure.restrict_map measurable_neg measurableSet_ball]
      have hneg_map : Measure.map (Neg.neg : ℂ → ℂ) volume = volume := hneg_mp.map_eq
      rw [hneg_map]
    have h1 : IntegrableOn (fun u : ℂ => -Real.log (tipDist (-u))) (ball u₀ r) := by
      have hint : Integrable (fun ζ => -Real.log (tipDist ζ)) (volume.restrict (ball (-u₀) r)) := havg_full.1
      rw [← hmap] at hint
      exact (integrable_map_measure hint.aestronglyMeasurable measurable_neg.aemeasurable).mp hint
    have h2 : ∫ u in ball u₀ r, (-Real.log (tipDist (-u))) =
        ∫ ζ in ball (-u₀) r, (-Real.log (tipDist ζ)) := by
      have hint : Integrable (fun ζ => -Real.log (tipDist ζ)) (volume.restrict (ball (-u₀) r)) := havg_full.1
      rw [← hmap] at hint ⊢
      exact (integral_map measurable_neg.aemeasurable hint.aestronglyMeasurable).symm
    exact ⟨h1, h2⟩
  by_cases hΨ0 : Ψ u₀ = 0
  · rw [hΨ0, norm_zero]
    have := airyEnv_pos u₀
    exact ⟨by positivity, fun _ => by positivity⟩
  -- Nonzero case: apply `subharmonic_disc_avg_le`
  have hzero_null : volume {u ∈ ball u₀ r | Ψ u = 0} = 0 :=
    ball_zero_set_measure_zero hr_pos (by linarith)
      (hΨ_an.mono fun u hu => hball_big hu) hΨ0
  let M_const : ℝ := Real.log C_0 + ς * √(R₁ + 2) - (4 / 3 : ℝ) * (u₀ ^ (3 / 2 : ℂ)).re + 1
  let B : ℂ → ℝ := fun u => M_const + (-Real.log (tipDist (-u)))
  have hB_int : IntegrableOn B (ball u₀ r) :=
    (integrableOn_const (by finiteness : volume (ball u₀ r) ≠ ⊤)).add hneg_int.1
  have hB_le : ∀ᵐ u ∂(volume.restrict (ball u₀ r)), Real.log ‖Ψ u‖ ≤ B u := by
    have h1_ae : ∀ᵐ u ∂volume, u ∉ ({u : ℂ | u.im = 0} : Set ℂ) :=
      ae_iff.mpr (by simpa using airy_volume_real_axis_zero)
    have h2_ae : ∀ᵐ u ∂volume, u ∉ {w ∈ ball u₀ r | Ψ w = 0} :=
      ae_iff.mpr (by simpa using hzero_null)
    filter_upwards [ae_restrict_mem measurableSet_ball, ae_restrict_of_ae h1_ae,
      ae_restrict_of_ae h2_ae] with u hu_ball hu_im hu_nz
    have hu_slit : ¬ (u.im = 0 ∧ u.re ≤ 0) := fun ⟨him, _⟩ => hu_im him
    have hu_ne0 : Ψ u ≠ 0 := fun h0 => hu_nz ⟨hu_ball, h0⟩
    have hu_dom : u ∈ closedBall (0 : ℂ) R_dom := hcl_sub (ball_subset_closedBall hu_ball)
    have hnorm_u : ‖u‖ ≤ R₁ + 2 := by
      have hd : ‖u - u₀‖ ≤ r := (dist_eq_norm u u₀ ▸ mem_ball.mp hu_ball).le
      calc ‖u‖ = ‖(u - u₀) + u₀‖ := by ring_nf
        _ ≤ ‖u - u₀‖ + ‖u₀‖ := norm_add_le _ _
        _ ≤ r + R₁ := add_le_add hd hu₀_norm
        _ ≤ R₁ + 2 := by linarith
    have hre_le : (u ^ (1 / 2 : ℂ)).re ≤ √(R₁ + 2) := by
      have hn : ‖u ^ (1 / 2 : ℂ)‖ = √‖u‖ := norm_cpow_half u
      exact (Complex.re_le_norm _).trans (hn ▸ Real.sqrt_le_sqrt hnorm_u)
    have hς_bd : ς * (u ^ (1 / 2 : ℂ)).re ≤ ς * √(R₁ + 2) :=
      mul_le_mul_of_nonneg_left hre_le hς
    have hosc := (abs_le.mp (typeII_exponent_oscillation hu_ball)).2
    have hu_re_pos : 0 < (u ^ (1 / 2 : ℂ)).re := by
      by_contra hle
      have h0 : (u ^ (1 / 2 : ℂ)).re = 0 := le_antisymm (not_lt.mp hle) (cpow_half_re_nonneg u)
      have him_u : u.im = 2 * (u ^ (1 / 2 : ℂ)).re * (u ^ (1 / 2 : ℂ)).im := (airySqrtRe_mul_im u).symm
      rw [h0] at him_u
      exact hu_im (by linarith)
    have hu_ne : u ≠ 0 := fun h0 => hu_im (by simp [h0])
    have hu_norm_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu_ne
    have hdist_eq : tipDist (-u) = √‖u‖ * (u ^ (1 / 2 : ℂ)).re := by
      unfold tipDist; rw [norm_neg, neg_neg]
    have hlog_dist : Real.log (‖u‖ ^ (-(1 / 2 : ℝ)) * ((u ^ (1 / 2 : ℂ)).re)⁻¹) =
        -Real.log (tipDist (-u)) := by
      rw [Real.rpow_neg hu_norm_pos.le, ← Real.sqrt_eq_rpow,
        Real.log_mul (inv_pos.mpr (Real.sqrt_pos.mpr hu_norm_pos)).ne' (inv_pos.mpr hu_re_pos).ne',
        Real.log_inv, Real.log_inv,
        hdist_eq, Real.log_mul (Real.sqrt_pos.mpr hu_norm_pos).ne' hu_re_pos.ne']
      ring
    have hlog_env := Real.log_le_log (norm_pos_iff.mpr hu_ne0) (hΨ_env u hu_dom hu_slit)
    have hpos_rhs : 0 < C_0 * airyEnv u * Real.exp (ς * (u ^ (1 / 2 : ℂ)).re) *
        (‖u‖ ^ (-(1 / 2 : ℝ)) * ((u ^ (1 / 2 : ℂ)).re)⁻¹) := by
      have := airyEnv_pos u; positivity
    have hlog_rhs : Real.log (C_0 * airyEnv u * Real.exp (ς * (u ^ (1 / 2 : ℂ)).re) *
          ‖u‖ ^ (-(1 / 2 : ℝ)) * ((u ^ (1 / 2 : ℂ)).re)⁻¹) =
        Real.log C_0 + (-(4 / 3 : ℝ) * (u ^ (3 / 2 : ℂ)).re) +
          ς * (u ^ (1 / 2 : ℂ)).re - Real.log (tipDist (-u)) := by
      rw [mul_assoc (C_0 * airyEnv u * Real.exp (ς * (u ^ (1 / 2 : ℂ)).re))]
      rw [Real.log_mul (mul_pos (mul_pos hC0 (airyEnv_pos u)) (Real.exp_pos _)).ne'
        (mul_pos (Real.rpow_pos_of_pos hu_norm_pos _) (inv_pos.mpr hu_re_pos)).ne',
        Real.log_mul (mul_pos hC0 (airyEnv_pos u)).ne' (Real.exp_pos _).ne',
        Real.log_mul hC0.ne' (airyEnv_pos u).ne',
        hlog_dist, Real.log_exp]
      unfold airyEnv
      rw [Real.log_exp]
      ring
    dsimp [B, M_const]
    linarith [hlog_env, hlog_rhs, hosc, hς_bd]
  have hsub := subharmonic_disc_avg_le hr_pos (hΨ_an.mono hcl_sub) hΨ0 hB_int hB_le
  have hB_avg : (π * r ^ 2)⁻¹ * ∫ u in ball u₀ r, B u =
      M_const + (π * r ^ 2)⁻¹ * ∫ ζ in ball (-u₀) r, (-Real.log (tipDist ζ)) := by
    dsimp [B]
    rw [integral_add (integrableOn_const (by finiteness : volume (ball u₀ r) ≠ ⊤)) hneg_int.1,
      setIntegral_const, hball_vol, smul_eq_mul, mul_add, hneg_int.2]
    congr 1
    field_simp [Real.pi_pos.ne', hr_pos.ne']
  rw [hB_avg] at hsub
  have h1_r : Real.log (1 / r) = Real.log 2 + (1 / 2 : ℝ) * Real.log (1 + ‖u₀‖) := by
    have hpos : 0 < 1 + ‖u₀‖ := by positivity
    have h1 : 1 / r = 2 * (1 + ‖u₀‖) ^ (1 / 2 : ℝ) := by
      dsimp [r]; rw [Real.rpow_neg hpos.le, one_div_mul_eq_div]; field_simp
    rw [h1, Real.log_mul two_pos.ne' (Real.rpow_pos_of_pos hpos _).ne', Real.log_rpow hpos]
  have h4pi : 4 / π ≤ 3 / 2 := by
    have := Real.pi_gt_three
    rw [div_le_div_iff₀ Real.pi_pos zero_lt_two]; linarith
  have hexp_14pi : Real.exp (1 + 4 / π) ≤ Real.exp (5 / 2) :=
    Real.exp_le_exp.mpr (by linarith)
  have h1_le_52 : Real.exp 1 ≤ Real.exp (5 / 2) := Real.exp_le_exp.mpr (by norm_num)
  refine ⟨?_, fun him => ?_⟩
  · have havg1 : (π * r ^ 2)⁻¹ * ∫ ζ in ball (-u₀) r, (-Real.log (tipDist ζ)) ≤
        Real.log 4 + 4 / π + (1 / 2 : ℝ) * Real.log (1 + ‖u₀‖) := by
      have h2 := havg_full.2.1
      have hlog4 : Real.log 4 = Real.log 2 + Real.log 2 := by
        rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul two_pos.ne' two_pos.ne']
      dsimp [r] at h2 ⊢
      linarith
    have hlog_bd : Real.log ‖Ψ u₀‖ ≤
        Real.log (4 * Real.exp (1 + 4 / π)) + Real.log C_0 + ς * √(R₁ + 2) +
          (-(4 / 3 : ℝ) * (u₀ ^ (3 / 2 : ℂ)).re) +
          (1 / 2 : ℝ) * Real.log (1 + ‖u₀‖) := by
      rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp]
      dsimp [M_const] at hsub
      linarith
    have hexp := Real.exp_le_exp.mpr hlog_bd
    rw [Real.exp_log (norm_pos_iff.mpr hΨ0)] at hexp
    have heq_rhs : Real.exp (Real.log (4 * Real.exp (1 + 4 / π)) + Real.log C_0 + ς * √(R₁ + 2) +
          (-(4 / 3 : ℝ) * (u₀ ^ (3 / 2 : ℂ)).re) + (1 / 2 : ℝ) * Real.log (1 + ‖u₀‖)) =
        4 * Real.exp (1 + 4 / π) * C_0 * Real.exp (ς * √(R₁ + 2)) *
          airyEnv u₀ * (1 + ‖u₀‖) ^ (1 / 2 : ℝ) := by
      have h1p : 0 < 1 + ‖u₀‖ := by positivity
      rw [Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_add,
        Real.exp_log (by positivity), Real.exp_log hC0,
        mul_comm (1 / 2 : ℝ) (Real.log (1 + ‖u₀‖)), ← Real.rpow_def_of_pos h1p]
      unfold airyEnv
      ring
    rw [heq_rhs] at hexp
    have h4e : 4 * Real.exp (1 + 4 / π) ≤ 8 * Real.exp (5 / 2) := by
      linarith [hexp_14pi, Real.exp_pos (5 / 2 : ℝ)]
    have hfac_nn : 0 ≤ C_0 * Real.exp (ς * √(R₁ + 2)) * airyEnv u₀ * (1 + ‖u₀‖) ^ (1 / 2 : ℝ) := by
      have := airyEnv_pos u₀; positivity
    calc ‖Ψ u₀‖ ≤ 4 * Real.exp (1 + 4 / π) * (C_0 * Real.exp (ς * √(R₁ + 2)) *
            airyEnv u₀ * (1 + ‖u₀‖) ^ (1 / 2 : ℝ)) := by linarith
      _ ≤ 8 * Real.exp (5 / 2) * (C_0 * Real.exp (ς * √(R₁ + 2)) *
            airyEnv u₀ * (1 + ‖u₀‖) ^ (1 / 2 : ℝ)) := mul_le_mul_of_nonneg_right h4e hfac_nn
      _ = _ := by ring
  · have him_neg : 2 * r ≤ |(-u₀).im| := by
      rw [Complex.neg_im, abs_neg]; exact him
    have havg2 := havg_full.2.2.1 him_neg
    rw [Complex.neg_im, abs_neg] at havg2
    have him_pos : 0 < |u₀.im| := lt_of_lt_of_le (by positivity) him
    have hlog_bd : Real.log ‖Ψ u₀‖ ≤
        Real.log (4 * Real.exp 1) + Real.log C_0 + ς * √(R₁ + 2) +
          (-(4 / 3 : ℝ) * (u₀ ^ (3 / 2 : ℂ)).re) + Real.log (1 / |u₀.im|) := by
      rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp,
        Real.log_div one_ne_zero him_pos.ne', Real.log_one, zero_sub]
      rw [Real.log_div (by norm_num) him_pos.ne'] at havg2
      dsimp [M_const] at hsub
      linarith
    have hexp := Real.exp_le_exp.mpr hlog_bd
    rw [Real.exp_log (norm_pos_iff.mpr hΨ0)] at hexp
    have heq_rhs : Real.exp (Real.log (4 * Real.exp 1) + Real.log C_0 + ς * √(R₁ + 2) +
          (-(4 / 3 : ℝ) * (u₀ ^ (3 / 2 : ℂ)).re) + Real.log (1 / |u₀.im|)) =
        4 * Real.exp 1 * C_0 * Real.exp (ς * √(R₁ + 2)) * airyEnv u₀ * (1 / |u₀.im|) := by
      rw [Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_add,
        Real.exp_log (by positivity), Real.exp_log hC0, Real.exp_log (one_div_pos.mpr him_pos)]
      unfold airyEnv; ring
    rw [heq_rhs] at hexp
    have h4e : 4 * Real.exp 1 ≤ 8 * Real.exp (5 / 2) := by
      linarith [h1_le_52, Real.exp_pos (5 / 2 : ℝ)]
    have hfac_nn : 0 ≤ C_0 * Real.exp (ς * √(R₁ + 2)) * airyEnv u₀ * (1 / |u₀.im|) := by
      have := airyEnv_pos u₀; positivity
    calc ‖Ψ u₀‖ ≤ 4 * Real.exp 1 * (C_0 * Real.exp (ς * √(R₁ + 2)) *
            airyEnv u₀ * (1 / |u₀.im|)) := by linarith
      _ ≤ 8 * Real.exp (5 / 2) * (C_0 * Real.exp (ς * √(R₁ + 2)) *
            airyEnv u₀ * (1 / |u₀.im|)) := mul_le_mul_of_nonneg_right h4e hfac_nn
      _ = _ := by ring

lemma airyEnv_le_exp_three_halves (u : ℂ) :
    airyEnv u ≤ Real.exp ((4 / 3 : ℝ) * ‖u‖ ^ (3 / 2 : ℝ)) := by
  unfold airyEnv
  apply Real.exp_le_exp.mpr
  have hnorm : ‖u ^ (3 / 2 : ℂ)‖ = ‖u‖ ^ (3 / 2 : ℝ) := by
    by_cases hu : u = 0
    · rw [hu, Complex.zero_cpow (by norm_num)]; simp
    · have hadd : u ^ (3 / 2 : ℂ) = u ^ (1 : ℂ) * u ^ (1 / 2 : ℂ) := by
        rw [← Complex.cpow_add _ _ hu]; congr 1; norm_num
      rw [hadd, Complex.cpow_one, norm_mul, norm_cpow_half u, Real.sqrt_eq_rpow]
      have hpos : 0 < ‖u‖ := norm_pos_iff.mpr hu
      rw [← Real.rpow_one_add' hpos.le (by norm_num : (1 : ℝ) + 1 / 2 ≠ 0)]
      norm_num
  have hre : -(‖u‖ ^ (3 / 2 : ℝ)) ≤ (u ^ (3 / 2 : ℂ)).re := by
    have := (abs_le.mp (Complex.abs_re_le_norm (u ^ (3 / 2 : ℂ)))).1
    linarith
  linarith

/-- Uniform cut-inclusive sup bound on `closedBall 0 R₁` (`R₁ + 2 ≤ R_dom`). -/
theorem typeII_cut_bound {Ψ : ℂ → ℂ} {R_dom R₁ C_0 ς : ℝ}
    (hR₁ : 0 ≤ R₁) (hR_dom : R₁ + 2 ≤ R_dom) (hC0 : 0 < C_0) (hς : 0 ≤ ς)
    (hΨ_an : AnalyticOnNhd ℂ Ψ (closedBall (0 : ℂ) R_dom))
    (hΨ_env : ∀ u ∈ closedBall (0 : ℂ) R_dom, ¬ (u.im = 0 ∧ u.re ≤ 0) →
      ‖Ψ u‖ ≤ C_0 * airyEnv u * Real.exp (ς * (u ^ (1 / 2 : ℂ)).re) *
        ‖u‖ ^ (-(1 / 2 : ℝ)) * ((u ^ (1 / 2 : ℂ)).re)⁻¹)
    (hς_one : ς * √(R₁ + 2) ≤ 1) {u₀ : ℂ} (hu₀ : u₀ ∈ closedBall (0 : ℂ) R₁) :
    ‖Ψ u₀‖ ≤ 8 * Real.exp (7 / 2) * C_0 * (1 + R₁) ^ (1 / 2 : ℝ) *
      Real.exp ((4 / 3 : ℝ) * R₁ ^ (3 / 2 : ℝ)) := by
  have h1 := (typeII_disc_avg_bound hR₁ hR_dom hC0 hς hΨ_an hΨ_env hu₀).1
  have hu₀_norm : ‖u₀‖ ≤ R₁ := mem_closedBall_zero_iff.mp hu₀
  have hrexp1 : Real.exp (ς * √(R₁ + 2)) ≤ Real.exp 1 := Real.exp_le_exp.mpr hς_one
  have he : airyEnv u₀ ≤ Real.exp ((4 / 3 : ℝ) * R₁ ^ (3 / 2 : ℝ)) :=
    (airyEnv_le_exp_three_halves u₀).trans
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (norm_nonneg _) hu₀_norm (by norm_num)) (by norm_num)))
  have h1p : (1 + ‖u₀‖) ^ (1 / 2 : ℝ) ≤ (1 + R₁) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
  have hexp72 : Real.exp (5 / 2) * Real.exp 1 = Real.exp (7 / 2) := by
    rw [← Real.exp_add]; norm_num
  calc ‖Ψ u₀‖
      ≤ 8 * Real.exp (5 / 2) * C_0 * Real.exp (ς * √(R₁ + 2)) *
          airyEnv u₀ * (1 + ‖u₀‖) ^ (1 / 2 : ℝ) := h1
    _ ≤ 8 * Real.exp (5 / 2) * C_0 * Real.exp 1 *
          Real.exp ((4 / 3 : ℝ) * R₁ ^ (3 / 2 : ℝ)) * (1 + R₁) ^ (1 / 2 : ℝ) := by
        have := airyEnv_pos u₀
        gcongr
    _ = 8 * Real.exp (7 / 2) * C_0 * (1 + R₁) ^ (1 / 2 : ℝ) *
          Real.exp ((4 / 3 : ℝ) * R₁ ^ (3 / 2 : ℝ)) := by
        rw [← hexp72]; ring

/-- Cauchy first- and second-derivative bounds on `closedBall 0 R₁` from a sup bound on `closedBall 0 (R₁ + 1)`. -/
lemma typeII_cauchy_deriv_bounds {Ψ : ℂ → ℂ} {R₁ M : ℝ}
    (hΨ_an : AnalyticOnNhd ℂ Ψ (closedBall (0 : ℂ) (R₁ + 1))) (_hM : 0 ≤ M)
    (hΨ_bd : ∀ u ∈ closedBall (0 : ℂ) (R₁ + 1), ‖Ψ u‖ ≤ M)
    {u₀ : ℂ} (hu₀ : u₀ ∈ closedBall (0 : ℂ) R₁) :
    ‖deriv Ψ u₀‖ ≤ M ∧ ‖iteratedDeriv 2 Ψ u₀‖ ≤ 2 * M := by
  have hu₀_norm : ‖u₀‖ ≤ R₁ := mem_closedBall_zero_iff.mp hu₀
  have hsub : closedBall u₀ 1 ⊆ closedBall (0 : ℂ) (R₁ + 1) := fun z hz => by
    rw [mem_closedBall, dist_zero_right]
    rw [mem_closedBall, dist_eq_norm] at hz
    calc ‖z‖ = ‖(z - u₀) + u₀‖ := by ring_nf
      _ ≤ ‖z - u₀‖ + ‖u₀‖ := norm_add_le _ _
      _ ≤ 1 + R₁ := add_le_add hz hu₀_norm
      _ = R₁ + 1 := by ring
  have hdiff : DiffContOnCl ℂ Ψ (ball u₀ 1) :=
    ⟨(hΨ_an.differentiableOn.mono (ball_subset_closedBall.trans hsub)),
      (hΨ_an.mono hsub).continuousOn.mono closure_ball_subset_closedBall⟩
  have hS : ∀ z ∈ sphere u₀ 1, ‖Ψ z‖ ≤ M := fun z hz =>
    hΨ_bd z (hsub (sphere_subset_closedBall hz))
  have hd1 := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le one_pos hdiff hS
  have hd2 := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 2 one_pos hdiff hS
  rw [div_one] at hd1
  simp only [Nat.factorial_two, Nat.cast_ofNat, one_pow, div_one] at hd2
  exact ⟨hd1, hd2⟩

/-- Explicit `r`-independent circle-`L¹` bound `C_circ_typeII` for `Step 3` (`TE.0`). -/
noncomputable def typeIICircConst (C_0 : ℝ) : ℝ :=
  16 * Real.exp (7 / 2) * C_0 + C_0 * Real.exp 1 * π * (2 * Real.log π + 1)

/-- For any `r ≥ 2` with `r + 2 ≤ R_dom` and `ς * √(r + 2) ≤ 1`, the circle ratio
`‖Ψ(r e^{iθ})‖ / airyEnv(r e^{iθ})` is dominated on `[-π, π]` by an integrable function `B`
whose integral over `[-π, π]` is at most `typeIICircConst C_0` (independent of `r`!). -/
theorem typeII_circle_env_majorant {Ψ : ℂ → ℂ} {R_dom r C_0 ς : ℝ}
    (hr : 2 ≤ r) (hr_dom : r + 2 ≤ R_dom) (hC0 : 0 < C_0) (hς : 0 ≤ ς)
    (hς_one : ς * √(r + 2) ≤ 1)
    (hΨ_an : AnalyticOnNhd ℂ Ψ (closedBall (0 : ℂ) R_dom))
    (hΨ_env : ∀ u ∈ closedBall (0 : ℂ) R_dom, ¬ (u.im = 0 ∧ u.re ≤ 0) →
      ‖Ψ u‖ ≤ C_0 * airyEnv u * Real.exp (ς * (u ^ (1 / 2 : ℂ)).re) *
        ‖u‖ ^ (-(1 / 2 : ℝ)) * ((u ^ (1 / 2 : ℂ)).re)⁻¹) :
    ∃ B : ℝ → ℝ, IntervalIntegrable B volume (-π) π ∧
      (∀ θ ∈ Icc (-π) π,
        ‖Ψ (circleMap 0 r θ)‖ / airyEnv (circleMap 0 r θ) ≤ B θ) ∧
      ∫ θ in (-π)..π, B θ ≤ typeIICircConst C_0 := by
  let δ : ℝ := (1 + r) ^ (-(1 / 2 : ℝ))
  have hδ_pos : 0 < δ := by positivity
  have h1r_ge3 : 3 ≤ 1 + r := by linarith
  have hδ_le1 : δ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
  have hδ_lt_pi2 : δ < π / 2 := by have := Real.pi_gt_three; linarith
  let M_edge : ℝ := 8 * Real.exp (5 / 2) * C_0 * Real.exp 1 * (1 + r) ^ (1 / 2 : ℝ)
  let M_mid : ℝ := C_0 * Real.exp 1 * π * r⁻¹
  let B : ℝ → ℝ := fun θ =>
    if |θ| ≤ π - δ then M_mid * (π - |θ|)⁻¹ else M_edge
  have hM_edge_nn : 0 ≤ M_edge := by positivity
  have hM_mid_nn : 0 ≤ M_mid := by positivity [Real.pi_pos]
  have hpt : ∀ θ ∈ Icc (-π) π,
      ‖Ψ (circleMap 0 r θ)‖ / airyEnv (circleMap 0 r θ) ≤ B θ := by
    intro θ _
    have hnorm : ‖circleMap 0 r θ‖ = r := by
      simp [norm_circleMap_zero, abs_of_pos (by linarith : 0 < r)]
    have hmem_r : circleMap 0 r θ ∈ closedBall (0 : ℂ) r := by
      rw [mem_closedBall_zero_iff, hnorm]
    have hmem_dom : circleMap 0 r θ ∈ closedBall (0 : ℂ) R_dom :=
      closedBall_subset_closedBall (by linarith) hmem_r
    have he_pos : 0 < airyEnv (circleMap 0 r θ) := airyEnv_pos _
    by_cases hmid : |θ| ≤ π - δ
    · have hB_eq : B θ = M_mid * (π - |θ|)⁻¹ := ite_eq_left hmid
      rw [hB_eq]
      have hθ_lt_pi : |θ| < π := lt_of_le_of_lt hmid (by linarith)
      have hθ_Ioo : θ ∈ Ioo (-π) π := abs_lt.mp hθ_lt_pi
      have harg_eq : (circleMap 0 r θ).arg = θ := by
        have hr_pos : 0 < r := by linarith
        rw [circleMap, zero_add, Complex.exp_mul_I]
        exact Complex.arg_mul_cos_add_sin_mul_I hr_pos ⟨hθ_Ioo.1, hθ_Ioo.2.le⟩
      have hnot_cut : ¬ ((circleMap 0 r θ).im = 0 ∧ (circleMap 0 r θ).re ≤ 0) := by
        intro ⟨him, hre⟩
        have hnz : circleMap 0 r θ ≠ 0 := by
          intro h0; rw [h0, norm_zero] at hnorm; linarith
        have harg_pi := Complex.arg_eq_pi_iff.mpr ⟨lt_of_le_of_ne hre
          (fun h => hnz (Complex.ext h him)), him⟩
        rw [harg_eq] at harg_pi
        linarith [hθ_Ioo.2]
      have hre_sqrt : ((circleMap 0 r θ) ^ (1 / 2 : ℂ)).re = √r * Real.cos (θ / 2) := by
        have hnz : circleMap 0 r θ ≠ 0 := by
          intro h0; rw [h0, norm_zero] at hnorm; linarith
        rw [Complex.cpow_def_of_ne_zero hnz, Complex.exp_re]
        have hre_log : (Complex.log (circleMap 0 r θ) * (1 / 2 : ℂ)).re = Real.log r / 2 := by
          simp [Complex.log_re, hnorm]; ring
        have him_log : (Complex.log (circleMap 0 r θ) * (1 / 2 : ℂ)).im = θ / 2 := by
          simp [Complex.log_im, harg_eq]; ring
        rw [hre_log, him_log, show Real.log r / 2 = Real.log r * (1 / 2 : ℝ) by ring,
          ← Real.rpow_def_of_pos (by linarith : 0 < r), ← Real.sqrt_eq_rpow]
      have hcos_lb : (π - |θ|) / π ≤ Real.cos (θ / 2) := by
        have hcos_eq : Real.cos (θ / 2) = Real.sin ((π - |θ|) / 2) := by
          rw [← Real.cos_abs (θ / 2), abs_div, abs_of_pos (zero_lt_two : (0 : ℝ) < 2),
            ← Real.sin_pi_div_two_sub]
          congr 1; ring
        rw [hcos_eq]
        have hx0 : 0 ≤ (π - |θ|) / 2 := by linarith [hθ_lt_pi]
        have hxpi2 : (π - |θ|) / 2 ≤ π / 2 := by linarith [abs_nonneg θ]
        calc (π - |θ|) / π = (2 / π) * ((π - |θ|) / 2) := by ring
          _ ≤ Real.sin ((π - |θ|) / 2) := Real.mul_le_sin hx0 hxpi2
      have hre_lb : √r * ((π - |θ|) / π) ≤ ((circleMap 0 r θ) ^ (1 / 2 : ℂ)).re := by
        rw [hre_sqrt]; exact mul_le_mul_of_nonneg_left hcos_lb (Real.sqrt_nonneg _)
      have hden_pos : 0 < √r * ((π - |θ|) / π) := by
        have : 0 < π - |θ| := by linarith
        positivity [Real.pi_pos]
      have hς_bd : ς * ((circleMap 0 r θ) ^ (1 / 2 : ℂ)).re ≤ 1 := by
        have h1 : ((circleMap 0 r θ) ^ (1 / 2 : ℂ)).re ≤ √(r + 2) := by
          rw [hre_sqrt]
          calc √r * Real.cos (θ / 2) ≤ √r * 1 := mul_le_mul_of_nonneg_left (Real.cos_le_one _) (Real.sqrt_nonneg _)
            _ = √r := mul_one _
            _ ≤ √(r + 2) := Real.sqrt_le_sqrt (by linarith)
        exact (mul_le_mul_of_nonneg_left h1 hς).trans hς_one
      have henv_bd := hΨ_env (circleMap 0 r θ) hmem_dom hnot_cut
      rw [hnorm] at henv_bd
      have hdiv : ‖Ψ (circleMap 0 r θ)‖ / airyEnv (circleMap 0 r θ) ≤
          C_0 * Real.exp (ς * ((circleMap 0 r θ) ^ (1 / 2 : ℂ)).re) *
            r ^ (-(1 / 2 : ℝ)) * (((circleMap 0 r θ) ^ (1 / 2 : ℂ)).re)⁻¹ := by
        rw [div_le_iff₀ he_pos]
        refine henv_bd.trans_eq (by ring)
      calc ‖Ψ (circleMap 0 r θ)‖ / airyEnv (circleMap 0 r θ)
          ≤ C_0 * Real.exp 1 * r ^ (-(1 / 2 : ℝ)) * (√r * ((π - |θ|) / π))⁻¹ := by
            have h1 : Real.exp (ς * ((circleMap 0 r θ) ^ (1 / 2 : ℂ)).re) ≤ Real.exp 1 :=
              Real.exp_le_exp.mpr hς_bd
            have h2 : (((circleMap 0 r θ) ^ (1 / 2 : ℂ)).re)⁻¹ ≤ (√r * ((π - |θ|) / π))⁻¹ :=
              inv_anti₀ hden_pos hre_lb
            have hr12_nn : 0 ≤ C_0 * Real.exp (ς * ((circleMap 0 r θ) ^ (1 / 2 : ℂ)).re) *
                r ^ (-(1 / 2 : ℝ)) := by positivity
            calc ‖Ψ (circleMap 0 r θ)‖ / airyEnv (circleMap 0 r θ)
                ≤ (C_0 * Real.exp (ς * ((circleMap 0 r θ) ^ (1 / 2 : ℂ)).re) * r ^ (-(1 / 2 : ℝ))) *
                    (((circleMap 0 r θ) ^ (1 / 2 : ℂ)).re)⁻¹ := hdiv
              _ ≤ (C_0 * Real.exp 1 * r ^ (-(1 / 2 : ℝ))) * (√r * ((π - |θ|) / π))⁻¹ :=
                  mul_le_mul (by gcongr) h2 (inv_nonneg.mpr (hden_pos.le.trans hre_lb))
                    (by positivity)
        _ = M_mid * (π - |θ|)⁻¹ := by
            dsimp [M_mid]
            rw [Real.rpow_neg (by linarith), ← Real.sqrt_eq_rpow]
            have hr_pos : 0 < r := by linarith
            have hsr : √r * √r = r := Real.mul_self_sqrt hr_pos.le
            have hsr_ne : √r ≠ 0 := (Real.sqrt_pos.mpr hr_pos).ne'
            have hpi_ne : π ≠ 0 := Real.pi_pos.ne'
            have hsub_ne : π - |θ| ≠ 0 := (by linarith : 0 < π - |θ|).ne'
            field_simp [hr_pos.ne', hsr_ne, hpi_ne, hsub_ne]
            rw [Real.sq_sqrt hr_pos.le]
    · have hB_eq : B θ = M_edge := ite_eq_right hmid
      rw [hB_eq]
      have hdisc := (typeII_disc_avg_bound (by linarith : 0 ≤ r) hr_dom hC0 hς hΨ_an hΨ_env hmem_r).1
      rw [hnorm] at hdisc
      have hdiv : ‖Ψ (circleMap 0 r θ)‖ / airyEnv (circleMap 0 r θ) ≤
          8 * Real.exp (5 / 2) * C_0 * Real.exp (ς * √(r + 2)) * (1 + r) ^ (1 / 2 : ℝ) := by
        rw [div_le_iff₀ he_pos]
        exact hdisc.trans_eq (by ring)
      refine hdiv.trans ?_
      have h1 : Real.exp (ς * √(r + 2)) ≤ Real.exp 1 := Real.exp_le_exp.mpr hς_one
      dsimp [M_edge]; gcongr
  -- Integrability of `B` via the three intervals `[-π, -(π-δ)]`, `[-(π-δ), π-δ]`, `[π-δ, π]`
  let a₁ : ℝ := -(π - δ)
  let a₂ : ℝ := π - δ
  have ha12 : a₁ ≤ a₂ := by dsimp [a₁, a₂]; linarith
  have hpi1 : -π ≤ a₁ := by dsimp [a₁]; linarith
  have h2pi : a₂ ≤ π := by dsimp [a₂]; linarith
  have hB_left_eq : EqOn B (fun _ => M_edge) (Ioo (-π) a₁) := fun θ hθ => by
    have hlt : π - δ < |θ| := by
      have : π - δ < -θ := by dsimp [a₁] at hθ; linarith [hθ.2]
      exact this.trans_le (neg_le_abs θ)
    exact ite_eq_right (not_le.mpr hlt)
  have hB_right_eq : EqOn B (fun _ => M_edge) (Ioo a₂ π) := fun θ hθ => by
    have hlt : π - δ < |θ| := by
      have : π - δ < θ := by dsimp [a₂] at hθ; linarith [hθ.1]
      exact this.trans_le (le_abs_self θ)
    exact ite_eq_right (not_le.mpr hlt)
  have hB_left_int : IntegrableOn B (Ioc (-π) a₁) := by
    rw [IntegrableOn, Measure.restrict_congr_set Ioo_ae_eq_Ioc.symm]
    exact (integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)).congr_fun
      hB_left_eq.symm measurableSet_Ioo
  have hB_right_int : IntegrableOn B (Ioc a₂ π) := by
    rw [IntegrableOn, Measure.restrict_congr_set Ioo_ae_eq_Ioc.symm]
    exact (integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)).congr_fun
      hB_right_eq.symm measurableSet_Ioo
  have hB_left : IntervalIntegrable B volume (-π) a₁ :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hpi1).mpr hB_left_int
  have hB_right : IntervalIntegrable B volume a₂ π :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le h2pi).mpr hB_right_int
  have hmid_cont : ContinuousOn (fun θ : ℝ => M_mid * (π - |θ|)⁻¹) (Icc a₁ a₂) := by
    refine continuousOn_const.mul (ContinuousOn.inv₀ (continuousOn_const.sub continuous_abs.continuousOn)
      fun θ hθ => ?_)
    have h1 : |θ| ≤ π - δ := abs_le.mpr ⟨by dsimp [a₁] at hθ; exact hθ.1, by dsimp [a₂] at hθ; exact hθ.2⟩
    linarith
  have hB_mid_eq : EqOn B (fun θ : ℝ => M_mid * (π - |θ|)⁻¹) (Icc a₁ a₂) := fun θ hθ =>
    ite_eq_left (abs_le.mpr ⟨by dsimp [a₁] at hθ; exact hθ.1, by dsimp [a₂] at hθ; exact hθ.2⟩)
  have hB_mid : IntervalIntegrable B volume a₁ a₂ :=
    ((hmid_cont.congr hB_mid_eq).mono (Set.uIcc_of_le ha12 ▸ Subset.rfl)).intervalIntegrable
  have hB_int : IntervalIntegrable B volume (-π) π :=
    (hB_left.trans hB_mid).trans hB_right
  refine ⟨B, hB_int, hpt, ?_⟩
  -- Evaluate the three integrals and sum
  have hint_split : ∫ θ in (-π)..π, B θ =
      (∫ θ in (-π)..a₁, B θ) + (∫ θ in a₁..a₂, B θ) + (∫ θ in a₂..π, B θ) := by
    have h1 := intervalIntegral.integral_add_adjacent_intervals hB_left hB_mid
    have h2 := intervalIntegral.integral_add_adjacent_intervals (hB_left.trans hB_mid) hB_right
    linarith
  have hint_left : ∫ θ in (-π)..a₁, B θ = δ * M_edge := by
    rw [intervalIntegral.integral_of_le hpi1, integral_Ioc_eq_integral_Ioo,
      setIntegral_congr_fun measurableSet_Ioo hB_left_eq, setIntegral_const,
      Measure.real_def, Real.volume_Ioo, ENNReal.toReal_ofReal (by dsimp [a₁]; linarith),
      smul_eq_mul]
    dsimp [a₁]; ring
  have hint_right : ∫ θ in a₂..π, B θ = δ * M_edge := by
    rw [intervalIntegral.integral_of_le h2pi, integral_Ioc_eq_integral_Ioo,
      setIntegral_congr_fun measurableSet_Ioo hB_right_eq, setIntegral_const,
      Measure.real_def, Real.volume_Ioo, ENNReal.toReal_ofReal (by dsimp [a₂]; linarith),
      smul_eq_mul]
    dsimp [a₂]; ring
  have hint_mid_pos : ∫ θ in (0 : ℝ)..a₂, M_mid * (π - θ)⁻¹ =
      M_mid * (Real.log π - Real.log δ) := by
    have ha2_nn : 0 ≤ a₂ := by dsimp [a₂]; linarith
    have hderiv : ∀ θ ∈ Set.uIcc 0 a₂,
        HasDerivAt (fun x => -(M_mid * Real.log (π - x))) (M_mid * (π - θ)⁻¹) θ := by
      intro θ hθ
      rw [Set.uIcc_of_le ha2_nn] at hθ
      have hpos : π - θ ≠ 0 := by dsimp [a₂] at hθ; linarith [hθ.2]
      have hd : HasDerivAt (fun x => π - x) (-1) θ := (hasDerivAt_id θ).const_sub π
      have hlog := hd.log hpos
      have hmul := (hlog.const_mul M_mid).neg
      refine hmul.congr_deriv ?_
      simp only [div_eq_mul_inv]; ring
    have hcont : ContinuousOn (fun θ : ℝ => M_mid * (π - θ)⁻¹) (Set.uIcc 0 a₂) := by
      rw [Set.uIcc_of_le ha2_nn]
      refine continuousOn_const.mul (ContinuousOn.inv₀ (continuousOn_const.sub continuousOn_id)
        fun θ hθ => by dsimp [a₂] at hθ; linarith [hθ.2])
    have hev := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
    rw [hev]
    simp only [sub_zero, show π - a₂ = δ by dsimp [a₂]; ring]
    ring
  have hint_mid_neg : ∫ θ in a₁..(0 : ℝ), M_mid * (π + θ)⁻¹ =
      M_mid * (Real.log π - Real.log δ) := by
    have hcomp := intervalIntegral.integral_comp_neg (fun θ => M_mid * (π - θ)⁻¹)
      (a := -a₂) (b := 0)
    have hsimp : ∫ θ in a₁..(0 : ℝ), M_mid * (π + θ)⁻¹ = ∫ θ in (0 : ℝ)..a₂, M_mid * (π - θ)⁻¹ := by
      have ha1_eq : a₁ = -a₂ := rfl
      rw [ha1_eq]
      simpa [sub_neg_eq_add, neg_zero, neg_neg] using hcomp
    rw [hsimp, hint_mid_pos]
  have hint_mid : ∫ θ in a₁..a₂, B θ = 2 * M_mid * (Real.log π - Real.log δ) := by
    have hmid_0 : a₁ ≤ 0 := by dsimp [a₁]; linarith
    have h0_a2 : 0 ≤ a₂ := by dsimp [a₂]; linarith
    have hI1 : IntervalIntegrable (fun θ => B θ) volume a₁ 0 :=
      hB_mid.mono_set (by rw [Set.uIcc_of_le ha12, Set.uIcc_of_le hmid_0]; exact Icc_subset_Icc_right h0_a2)
    have hI2 : IntervalIntegrable (fun θ => B θ) volume 0 a₂ :=
      hB_mid.mono_set (by rw [Set.uIcc_of_le ha12, Set.uIcc_of_le h0_a2]; exact Icc_subset_Icc_left hmid_0)
    have h1eq : ∫ θ in a₁..(0 : ℝ), B θ = ∫ θ in a₁..(0 : ℝ), M_mid * (π + θ)⁻¹ := by
      refine intervalIntegral.integral_congr fun θ hθ => ?_
      rw [Set.uIcc_of_le hmid_0] at hθ
      rw [hB_mid_eq ⟨hθ.1, hθ.2.trans h0_a2⟩]
      dsimp only
      rw [abs_of_nonpos hθ.2]; ring_nf
    have h2eq : ∫ θ in (0 : ℝ)..a₂, B θ = ∫ θ in (0 : ℝ)..a₂, M_mid * (π - θ)⁻¹ := by
      refine intervalIntegral.integral_congr fun θ hθ => ?_
      rw [Set.uIcc_of_le h0_a2] at hθ
      rw [hB_mid_eq ⟨hmid_0.trans hθ.1, hθ.2⟩]
      dsimp only
      rw [abs_of_nonneg hθ.1]
    rw [← intervalIntegral.integral_add_adjacent_intervals hI1 hI2, h1eq, h2eq,
      hint_mid_neg, hint_mid_pos]
    ring
  -- Combine numerical bounds
  have hedge_val : δ * M_edge = 8 * Real.exp (7 / 2) * C_0 := by
    have hpow : (1 + r) ^ (-(1 / 2 : ℝ)) * (1 + r) ^ (1 / 2 : ℝ) = 1 := by
      rw [← Real.rpow_add (by linarith), neg_add_cancel, Real.rpow_zero]
    have hexp72 : Real.exp (5 / 2) * Real.exp 1 = Real.exp (7 / 2) := by
      rw [← Real.exp_add]; norm_num
    dsimp [δ, M_edge]
    calc (1 + r) ^ (-(1 / 2 : ℝ)) * (8 * Real.exp (5 / 2) * C_0 * Real.exp 1 * (1 + r) ^ (1 / 2 : ℝ))
        = 8 * C_0 * (Real.exp (5 / 2) * Real.exp 1) * ((1 + r) ^ (-(1 / 2 : ℝ)) * (1 + r) ^ (1 / 2 : ℝ)) := by ring
      _ = 8 * Real.exp (7 / 2) * C_0 := by rw [hpow, hexp72]; ring
  have hlog_δ : Real.log π - Real.log δ ≤ Real.log π + r / 2 := by
    have hneg_δ : -Real.log δ = (1 / 2 : ℝ) * Real.log (1 + r) := by
      dsimp [δ]
      rw [Real.log_rpow (by linarith)]
      ring
    have hlog_r : Real.log (1 + r) ≤ r := Real.log_le_sub_one_of_pos (by linarith) |>.trans_eq (by ring)
    linarith
  have hmid_bd : 2 * M_mid * (Real.log π - Real.log δ) ≤
      C_0 * Real.exp 1 * π * (2 * Real.log π + 1) := by
    have hr_pos : 0 < r := by linarith
    have hmul1 : 2 * M_mid * (Real.log π - Real.log δ) ≤
        2 * M_mid * (Real.log π + r / 2) :=
      mul_le_mul_of_nonneg_left hlog_δ (by positivity)
    have hlogπ_nn : 0 ≤ Real.log π := Real.log_nonneg (by have := Real.pi_gt_three; linarith)
    have hinv_le1 : r⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
    calc 2 * M_mid * (Real.log π - Real.log δ)
        ≤ 2 * M_mid * (Real.log π + r / 2) := hmul1
      _ = C_0 * Real.exp 1 * π * (2 * r⁻¹ * Real.log π + 1) := by
          dsimp [M_mid]; field_simp [hr_pos.ne']
      _ ≤ C_0 * Real.exp 1 * π * (2 * (1 : ℝ) * Real.log π + 1) := by
          gcongr
      _ = C_0 * Real.exp 1 * π * (2 * Real.log π + 1) := by ring
  rw [hint_split, hint_left, hint_mid, hint_right, hedge_val]
  unfold typeIICircConst
  linarith

end FormalResearch.ModularBootstrap.ConcreteBootstrap

