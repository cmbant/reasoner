module

public import FormalResearch.ModularBootstrap.Blowup.Majorant
public import FormalResearch.ModularBootstrap.Rigidity.AiryRigidity
public import FormalResearch.Complex.Montel

/-!
# Proposition T (blow-up at the tip) and Theorems C, R1--R3 (`blowup_limit.tex`)

Formalizes the main theorem of `CFT/modular_bootstrap/paper/blowup_limit.tex`:
* `tipRescale_pointwise_envelope`: uniform local pointwise bounds for `Φ_c = tipRescale c' test`
  via Lemma T5 (`lemma_T5`), subharmonic disc averaging (`subharmonic_disc_avg_le`), and the
  logarithmic tip-distance disc average (`disc_avg_neg_log_tipDist`). Includes the global
  `C (1 + |ζ|)^{1/2} e^{H(ζ)}`, off-axis sharp `C e^{H(ζ)} (1 + min((1 + |ζ|)^{1/2}, 1/|Im ζ|))`,
  and sector gain `C e^{H(ζ)} / |ζ|` bounds.
* `montel_exhaustion_entire`: diagonal Montel exhaustion on expanding discs `ball 0 (k + 1)`
  producing a locally uniformly convergent subsequence on `ℂ` with an entire limit.
* `blowup_left_tail_bound`: uniform left-tail estimate
  `∫ s in Ioc (tipSMin c') (-R), ‖Φ_c(s)‖ ≤ η(R)` with `η(R) → 0` as `R → ∞` (for
  `1 ≤ R` and eventually in `c' → ∞`), combining deep-lobe decay (`hDeepLobe`) and
  `proposition_M` in the Airy band.
* `proposition_T`: full **Proposition T** (i)–(vi) (`blowup_limit.tex`, Proposition `bl:T`)
  for any sequence of concrete `BlowupTest`s with `c' → ∞` and upper-bounded tip thresholds `s₁`,
  noting the exact left cutoff `Ioc (tipSMin c')` for finite `c'` (cf. `report.md` TeX issue 1).
* `blowupFamilyPackage_of_tests`, `isThreshold_imp_g_t1_eq_zero`, `rigidityFamilyPackage_of_tests`:
  constructs `BlowupFamilyPackage` and `RigidityFamilyPackage` (`Rigidity/AiryRigidity.lean`)
  from a family of `BlowupTest`s plus minimal-threshold `g t₁ = 0` (`rigidity.tex`), discharging
  `propT_subseq` and connecting directly to `theorem_C` and `theorem_R1`–`theorem_R3`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real ENNReal

namespace FormalResearch.ModularBootstrap

open FormalResearch.Special
open FormalResearch.ArgPrinciple
open FormalResearch.Analysis

/-! ### Section 1: Pointwise envelope from Lemma T5 + subharmonic disc averaging -/

private lemma volume_real_axis_zero : volume {ζ : ℂ | ζ.im = 0} = 0 := by
  let L : Submodule ℝ ℂ := LinearMap.ker Complex.imCLM.toLinearMap
  have hne : L ≠ ⊤ := by
    intro htop
    have hI : I ∈ L := htop ▸ Submodule.mem_top
    have h0 : Complex.imCLM.toLinearMap I = 0 := hI
    simp at h0
  have hsub : {ζ : ℂ | ζ.im = 0} = (L : Set ℂ) := by
    ext ζ; simp [L, LinearMap.mem_ker]
  rw [hsub]
  exact MeasureTheory.Measure.addHaar_submodule volume L hne

private lemma analytic_zero_set_ball_measure_zero {f : ℂ → ℂ} {ζ₀ : ℂ} {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hf : AnalyticOnNhd ℂ f (ball ζ₀ R)) (hf0 : f ζ₀ ≠ 0) :
    volume {ζ ∈ ball ζ₀ r | f ζ = 0} = 0 := by
  classical
  have hnot_zero : ¬ EqOn f 0 (ball ζ₀ R) := fun h => hf0 (h (mem_ball_self (hr.trans hrR)))
  have hev : ∀ z ∈ ball ζ₀ R, ∀ᶠ w in 𝓝[≠] z, f w ≠ 0 := by
    rcases hf.eqOn_zero_or_eventually_ne_zero_of_preconnected (convex_ball ζ₀ R).isPreconnected with
      h | h
    · exact absurd h hnot_zero
    · intro z hz
      have h1 := mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp h z hz
      have h2 : ball ζ₀ R ∈ 𝓝[≠] z := nhdsWithin_le_nhds (isOpen_ball.mem_nhds hz)
      filter_upwards [h1, h2] with w hw1 hw2
      rcases hw1 with hw | hw
      · exact hw
      · exact absurd hw2 hw
  have hopen : ∀ z ∈ closedBall ζ₀ r, ∃ δ > 0, ∀ w ∈ ball z δ, w ≠ z → f w ≠ 0 := fun z hz => by
    have hzR : z ∈ ball ζ₀ R := closedBall_subset_ball hrR hz
    have h1 := (hev z hzR).exists_mem
    obtain ⟨U, hU, hUf⟩ := h1
    rw [mem_nhdsWithin] at hU
    obtain ⟨V, hV_open, hzV, hVU⟩ := hU
    obtain ⟨δ, hδ_pos, hδ_sub⟩ := Metric.isOpen_iff.mp hV_open z hzV
    exact ⟨δ, hδ_pos, fun w hw hwz => hUf w (hVU ⟨hδ_sub hw, hwz⟩)⟩
  choose δ hδ_pos hδ_ne using hopen
  obtain ⟨s, hs⟩ := (isCompact_closedBall ζ₀ r).elim_nhds_subcover
    (fun z => if hz : z ∈ closedBall ζ₀ r then ball z (δ z hz) else ∅)
    fun z hz => by
      simp only [hz, ↓reduceDIte]
      exact ball_mem_nhds z (hδ_pos z hz)
  have hsub : {ζ ∈ ball ζ₀ r | f ζ = 0} ⊆ (s : Set ℂ) := by
    intro ζ ⟨hζ_ball, hζ_f0⟩
    have hζ_cl : ζ ∈ closedBall ζ₀ r := ball_subset_closedBall hζ_ball
    obtain ⟨z, hzs, hζ_in⟩ := mem_iUnion₂.mp (hs.2 hζ_cl)
    have hz_cl : z ∈ closedBall ζ₀ r := hs.1 z hzs
    simp only [hz_cl, ↓reduceDIte] at hζ_in
    by_contra hne
    exact absurd hζ_f0 (hδ_ne z hz_cl ζ hζ_in fun h_eq => hne (h_eq ▸ hzs))
  exact measure_mono_null hsub (s.finite_toSet.measure_zero volume)

/-- Uniform local pointwise estimates for `tipRescale` (`blowup_limit.tex`, Proposition T (i) and §3):
for every `R ≥ 0`, eventually as `c' → ∞`, for all `test : BlowupTest inp c'` and all
`ζ₀ ∈ closedBall 0 R`:
1) `‖Φ_c(ζ₀)‖ ≤ C_env * (1 + ‖ζ₀‖)^(1/2) * exp (tipH ζ₀)`
2) if `ζ₀.im ≠ 0`, `‖Φ_c(ζ₀)‖ ≤ C_env * exp (tipH ζ₀) * (1 + min ((1 + ‖ζ₀‖)^(1/2)) (1 / |ζ₀.im|))`
3) if `|(-ζ₀).arg| ≤ 2π/3` and `8 ≤ ‖ζ₀‖`, `‖Φ_c(ζ₀)‖ ≤ C_env * exp (tipH ζ₀) / ‖ζ₀‖`. -/
theorem tipRescale_pointwise_envelope (hI0 : BesselI0Asymptotic) (inp : StripBootstrapInputs) :
    ∃ C_env : ℝ, 0 ≤ C_env ∧
      ∀ R : ℝ, 0 ≤ R → ∀ᶠ c' : ℝ in atTop,
        ∀ (test : BlowupTest inp c') (ζ₀ : ℂ), ζ₀ ∈ closedBall (0 : ℂ) R →
          ‖tipRescale c' test ζ₀‖ ≤ C_env * (1 + ‖ζ₀‖) ^ (1 / 2 : ℝ) * Real.exp (tipH ζ₀) ∧
          (ζ₀.im ≠ 0 → ‖tipRescale c' test ζ₀‖ ≤
            C_env * Real.exp (tipH ζ₀) *
              (1 + min ((1 + ‖ζ₀‖) ^ (1 / 2 : ℝ)) (1 / |ζ₀.im|))) ∧
          (|(-ζ₀).arg| ≤ 2 * π / 3 → 8 ≤ ‖ζ₀‖ →
            ‖tipRescale c' test ζ₀‖ ≤ C_env * Real.exp (tipH ζ₀) / ‖ζ₀‖) := by
  obtain ⟨ρ_T5, C₁, C₂, C₃, c₀, hρ_pos, hCT2_nn, hCT3_nn, hc₀_39, hT5⟩ := lemma_T5 hI0 inp
  let C_env : ℝ := Real.exp (3 * KTip / 4 + |C₁| + Real.log 4 + 4 / π + 1)
  have hCenv_pos : 0 < C_env := Real.exp_pos _
  refine ⟨C_env, hCenv_pos.le, fun R hR => ?_⟩
  have hε_tend : Tendsto (fun c' : ℝ => tipEps c' * (R + 1)) atTop (nhds 0) := by
    have h0 := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3))
    simpa [tipEps] using h0.mul_const (R + 1)
  have hlog_tend : Tendsto (fun c' : ℝ =>
      C₂ * tipEps c' * (R + 1) ^ (5 / 2 : ℝ) +
        C₃ * (tipEps c' * (R + 1)) ^ (1 / 2 : ℝ) * Real.log c') atTop (nhds 0) := by
    have ht1 : Tendsto (fun c' : ℝ => C₂ * tipEps c' * (R + 1) ^ (5 / 2 : ℝ)) atTop (nhds 0) := by
      have h0 := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3))
      have h1 := (h0.const_mul C₂).mul_const ((R + 1) ^ (5 / 2 : ℝ))
      simpa [tipEps] using h1
    have ht2 : Tendsto (fun c' : ℝ =>
        C₃ * (tipEps c' * (R + 1)) ^ (1 / 2 : ℝ) * Real.log c') atTop (nhds 0) := by
      have hmul : Tendsto (fun c' : ℝ => Real.log c' / c' ^ (1 / 3 : ℝ)) atTop (nhds 0) := by
        have h0 : Tendsto (fun c' : ℝ => 6 * c' ^ (-(1 / 6 : ℝ))) atTop (nhds 0) := by
          simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 6)).const_mul 6
        refine squeeze_zero' ?_ ?_ h0
        · filter_upwards [eventually_ge_atTop (1 : ℝ)] with c' hc'
          exact div_nonneg (Real.log_nonneg hc') (by positivity)
        · filter_upwards [eventually_ge_atTop (1 : ℝ)] with c' hc'
          have hc'_pos : 0 < c' := by linarith
          have hlog : Real.log c' ≤ 6 * c' ^ (1 / 6 : ℝ) := by
            have hl := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hc'_pos (1 / 6 : ℝ))
            have h6 : Real.log c' = 6 * Real.log (c' ^ (1 / 6 : ℝ)) := by
              rw [Real.log_rpow hc'_pos]; ring
            linarith
          have hpow : c' ^ (1 / 6 : ℝ) / c' ^ (1 / 3 : ℝ) = c' ^ (-(1 / 6 : ℝ)) := by
            rw [div_eq_mul_inv, ← Real.rpow_neg hc'_pos.le, ← Real.rpow_add hc'_pos]; norm_num
          calc Real.log c' / c' ^ (1 / 3 : ℝ)
              ≤ (6 * c' ^ (1 / 6 : ℝ)) / c' ^ (1 / 3 : ℝ) := by gcongr
            _ = 6 * (c' ^ (1 / 6 : ℝ) / c' ^ (1 / 3 : ℝ)) := by ring
            _ = 6 * c' ^ (-(1 / 6 : ℝ)) := by rw [hpow]
      have hrew : ∀ᶠ c' : ℝ in atTop,
          C₃ * (tipEps c' * (R + 1)) ^ (1 / 2 : ℝ) * Real.log c' =
            (C₃ * (R + 1) ^ (1 / 2 : ℝ)) * (Real.log c' / c' ^ (1 / 3 : ℝ)) := by
        filter_upwards [eventually_ge_atTop (1 : ℝ)] with c' hc'
        have hc'_pos : 0 < c' := by linarith
        unfold tipEps
        rw [Real.mul_rpow (Real.rpow_nonneg hc'_pos.le _) (by linarith),
          ← Real.rpow_mul hc'_pos.le, show -(2 / 3 : ℝ) * (1 / 2 : ℝ) = -(1 / 3 : ℝ) by norm_num,
          Real.rpow_neg hc'_pos.le]
        ring
      exact ((hmul.const_mul (C₃ * (R + 1) ^ (1 / 2 : ℝ))).congr' (hrew.mono fun _ h => h.symm)).trans
        (by simp)
    simpa using ht1.add ht2
  filter_upwards [eventually_ge_atTop c₀,
    hε_tend.eventually (eventually_le_nhds hρ_pos),
    hε_tend.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    hlog_tend.eventually (eventually_lt_nhds zero_lt_one)] with
    c' hc' hεR_ρ hεR_half herr_le_lt
  have herr_le : C₂ * tipEps c' * (R + 1) ^ (5 / 2 : ℝ) +
      C₃ * (tipEps c' * (R + 1)) ^ (1 / 2 : ℝ) * Real.log c' ≤ 1 := herr_le_lt.le
  have hc'_pos : 0 < c' := by linarith [hc₀_39]
  have hc'_gt1 : 1 < c' := by linarith [hc₀_39]
  have hε_pos : 0 < tipEps c' := tipEps_pos hc'_pos
  intro test ζ₀ hζ₀
  have hζ₀_norm : ‖ζ₀‖ ≤ R := by simpa [mem_closedBall, dist_zero_right] using hζ₀
  have hεζ_1 : tipEps c' * (R + 1) ≤ ρ_T5 := hεR_ρ
  let r : ℝ := (1 / 2 : ℝ) * (1 + ‖ζ₀‖) ^ (-(1 / 2 : ℝ))
  have hr_pos : 0 < r := by positivity
  have hr_le_half : r ≤ 1 / 2 := by
    have : (1 + ‖ζ₀‖) ^ (-(1 / 2 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg ζ₀]) (by norm_num)
    dsimp [r]; linarith
  have hball_sub : closedBall ζ₀ r ⊆ ball (0 : ℂ) (R + 1) := by
    intro ζ hζ
    rw [mem_ball, dist_zero_right]
    have h1 := mem_closedBall.mp hζ
    rw [dist_eq_norm] at h1
    calc ‖ζ‖ = ‖(ζ - ζ₀) + ζ₀‖ := by ring_nf
      _ ≤ ‖ζ - ζ₀‖ + ‖ζ₀‖ := norm_add_le _ _
      _ ≤ r + R := add_le_add h1 hζ₀_norm
      _ < R + 1 := by linarith
  have hholo_ball : DifferentiableOn ℂ (tipRescale c' test) (ball (0 : ℂ) (R + 1)) :=
    tipRescale_holo_ball hc'_pos (by linarith) test
  have han_ball : AnalyticOnNhd ℂ (tipRescale c' test) (ball (0 : ℂ) (R + 1)) :=
    hholo_ball.analyticOnNhd isOpen_ball
  by_cases hzero : tipRescale c' test ζ₀ = 0
  · rw [hzero, norm_zero]
    refine ⟨by positivity [Real.exp_pos (tipH ζ₀)], fun _ => by positivity [Real.exp_pos (tipH ζ₀)],
      fun _ h8 => by positivity [Real.exp_pos (tipH ζ₀)]⟩
  · have hzero_null : volume {ζ ∈ ball ζ₀ r | tipRescale c' test ζ = 0} = 0 := by
      have han_big : AnalyticOnNhd ℂ (tipRescale c' test) (ball ζ₀ (r + 1 / 4)) := by
        refine han_ball.mono fun ζ hζ => ?_
        rw [mem_ball, dist_zero_right]
        rw [mem_ball, dist_eq_norm] at hζ
        calc ‖ζ‖ = ‖(ζ - ζ₀) + ζ₀‖ := by ring_nf
          _ ≤ ‖ζ - ζ₀‖ + ‖ζ₀‖ := norm_add_le _ _
          _ < r + 1 / 4 + ‖ζ₀‖ := by linarith
          _ < R + 1 := by linarith
      exact analytic_zero_set_ball_measure_zero hr_pos (by linarith) han_big hzero
    let M_const : ℝ := tipH ζ₀ + 3 * KTip / 4 + |C₁| + 1
    let B : ℂ → ℝ := fun ζ => M_const + (-Real.log (tipDist ζ))
    have havg := disc_avg_neg_log_tipDist ζ₀
    have hB_int : IntegrableOn B (ball ζ₀ r) :=
      (integrableOn_const (by finiteness : volume (ball ζ₀ r) ≠ ⊤)).add havg.1
    have hB_le : ∀ᵐ ζ ∂(volume.restrict (ball ζ₀ r)),
        Real.log ‖tipRescale c' test ζ‖ ≤ B ζ := by
      have h1_ae : ∀ᵐ ζ ∂volume, ζ ∉ ({ζ : ℂ | ζ.im = 0} : Set ℂ) :=
        ae_iff.mpr (by simpa using volume_real_axis_zero)
      have h2_ae : ∀ᵐ ζ ∂volume, ζ ∉ {w ∈ ball ζ₀ r | tipRescale c' test w = 0} :=
        ae_iff.mpr (by simpa using hzero_null)
      filter_upwards [ae_restrict_mem measurableSet_ball, ae_restrict_of_ae h1_ae,
        ae_restrict_of_ae h2_ae] with ζ hζ_ball hζ_im hζ_nz
      have hζ_slit : ¬ (ζ.im = 0 ∧ 0 ≤ ζ.re) := fun ⟨him, _⟩ => hζ_im him
      have hζ_ne0 : tipRescale c' test ζ ≠ 0 := fun h0 => hζ_nz ⟨hζ_ball, h0⟩
      have hζ_R : ‖ζ‖ ≤ R + 1 := by
        rw [← dist_zero_right ζ]
        exact (mem_ball.mp (hball_sub (ball_subset_closedBall hζ_ball))).le
      have hεζ_le : tipEps c' * ‖ζ‖ ≤ ρ_T5 :=
        (mul_le_mul_of_nonneg_left hζ_R hε_pos.le).trans hεζ_1
      have hT5_bd := hT5 test hc' hζ_slit hεζ_le hζ_ne0
      have hosc := (abs_le.mp (tipH_disc_oscillation ζ₀ ζ hζ_ball)).2
      have herr_pt : C₂ * tipEps c' * ‖ζ‖ ^ (5 / 2 : ℝ) +
          C₃ * (tipEps c' * ‖ζ‖) ^ (1 / 2 : ℝ) * Real.log c' ≤ 1 := by
        have hlogc'_nn : 0 ≤ Real.log c' := Real.log_nonneg hc'_gt1.le
        have h1' : C₂ * tipEps c' * ‖ζ‖ ^ (5 / 2 : ℝ) ≤ C₂ * tipEps c' * (R + 1) ^ (5 / 2 : ℝ) := by
          gcongr
        have h2' : C₃ * (tipEps c' * ‖ζ‖) ^ (1 / 2 : ℝ) * Real.log c' ≤
            C₃ * (tipEps c' * (R + 1)) ^ (1 / 2 : ℝ) * Real.log c' := by
          gcongr
        linarith
      have hC₁_le : C₁ ≤ |C₁| := le_abs_self C₁
      dsimp [B, M_const]
      linarith
    have hsub := subharmonic_disc_avg_le hr_pos (fun ζ hζ => han_ball ζ (hball_sub hζ))
      hzero hB_int hB_le
    have hball_vol : volume.real (ball ζ₀ r) = π * r ^ 2 := by
      rw [Measure.real_def, Complex.volume_ball, ENNReal.toReal_mul, ENNReal.toReal_pow,
        ENNReal.toReal_ofReal hr_pos.le, ENNReal.coe_toReal, NNReal.coe_real_pi]
      ring
    have hB_avg : (π * r ^ 2)⁻¹ * ∫ ζ in ball ζ₀ r, B ζ =
        M_const + (π * r ^ 2)⁻¹ * ∫ ζ in ball ζ₀ r, (-Real.log (tipDist ζ)) := by
      dsimp [B]
      rw [integral_add (integrableOn_const (by finiteness : volume (ball ζ₀ r) ≠ ⊤)) havg.1,
        setIntegral_const, hball_vol, smul_eq_mul, mul_add]
      congr 1
      field_simp [Real.pi_pos.ne', hr_pos.ne']
    rw [hB_avg] at hsub
    have hlog_bd1 : Real.log ‖tipRescale c' test ζ₀‖ ≤
        tipH ζ₀ + Real.log C_env + (1 / 2 : ℝ) * Real.log (1 + ‖ζ₀‖) := by
      have h1_r : Real.log (1 / r) = Real.log 2 + (1 / 2 : ℝ) * Real.log (1 + ‖ζ₀‖) := by
        have hpos : 0 < 1 + ‖ζ₀‖ := by positivity
        have h1 : 1 / r = 2 * (1 + ‖ζ₀‖) ^ (1 / 2 : ℝ) := by
          dsimp [r]; rw [Real.rpow_neg hpos.le, one_div_mul_eq_div]; field_simp
        rw [h1, Real.log_mul two_pos.ne' (Real.rpow_pos_of_pos hpos _).ne',
          Real.log_rpow hpos]
      have hlog4 : Real.log 4 = Real.log 2 + Real.log 2 := by
        rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul two_pos.ne' two_pos.ne']
      have hC_log : Real.log C_env = 3 * KTip / 4 + |C₁| + Real.log 4 + 4 / π + 1 := Real.log_exp _
      dsimp [M_const] at hsub
      linarith [havg.2.1]
    have hbd1 : ‖tipRescale c' test ζ₀‖ ≤
        C_env * (1 + ‖ζ₀‖) ^ (1 / 2 : ℝ) * Real.exp (tipH ζ₀) := by
      have hexp := Real.exp_le_exp.mpr hlog_bd1
      rw [Real.exp_log (norm_pos_iff.mpr hzero), Real.exp_add, Real.exp_add,
        Real.exp_log hCenv_pos, mul_comm (1 / 2 : ℝ) (Real.log (1 + ‖ζ₀‖)),
        ← Real.rpow_def_of_pos (by positivity : 0 < 1 + ‖ζ₀‖)] at hexp
      exact hexp.trans_eq (by ring)
    refine ⟨hbd1, fun him_ne => ?_, fun harg hnorm8 => ?_⟩
    · have him_pos : 0 < |ζ₀.im| := abs_pos.mpr him_ne
      rcases le_or_gt (2 * r) |ζ₀.im| with h2r | h2r
      · have hlog_bd2 : Real.log ‖tipRescale c' test ζ₀‖ ≤
            tipH ζ₀ + Real.log C_env + Real.log (1 / |ζ₀.im|) := by
          have hlog4im : Real.log (4 / |ζ₀.im|) = Real.log 4 + Real.log (1 / |ζ₀.im|) := by
            rw [div_eq_mul_one_div, Real.log_mul (by norm_num) (one_div_pos.mpr him_pos).ne']
          have hC_log : Real.log C_env = 3 * KTip / 4 + |C₁| + Real.log 4 + 4 / π + 1 := Real.log_exp _
          have hpi_nn : 0 ≤ 4 / π := by positivity
          dsimp [M_const] at hsub
          linarith [havg.2.2.1 h2r]
        have hexp := Real.exp_le_exp.mpr hlog_bd2
        rw [Real.exp_log (norm_pos_iff.mpr hzero), Real.exp_add, Real.exp_add,
          Real.exp_log hCenv_pos, Real.exp_log (one_div_pos.mpr him_pos)] at hexp
        have hmin_eq : min ((1 + ‖ζ₀‖) ^ (1 / 2 : ℝ)) (1 / |ζ₀.im|) = 1 / |ζ₀.im| := by
          refine min_eq_right ?_
          have h2r_eq : (1 + ‖ζ₀‖) ^ (1 / 2 : ℝ) = (2 * r)⁻¹ := by
            dsimp [r]
            rw [← mul_assoc, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_mul,
              Real.rpow_neg (by positivity), inv_inv]
          rw [h2r_eq, one_div]
          exact inv_anti₀ (by positivity) h2r
        rw [hmin_eq]
        calc ‖tipRescale c' test ζ₀‖ ≤ Real.exp (tipH ζ₀) * C_env * (1 / |ζ₀.im|) := hexp
          _ ≤ C_env * Real.exp (tipH ζ₀) * (1 + 1 / |ζ₀.im|) := by
              have : 0 ≤ C_env * Real.exp (tipH ζ₀) := by positivity
              nlinarith
      · have hmin_eq : min ((1 + ‖ζ₀‖) ^ (1 / 2 : ℝ)) (1 / |ζ₀.im|) = (1 + ‖ζ₀‖) ^ (1 / 2 : ℝ) := by
          refine min_eq_left ?_
          have h2r_eq : (1 + ‖ζ₀‖) ^ (1 / 2 : ℝ) = (2 * r)⁻¹ := by
            dsimp [r]
            rw [← mul_assoc, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_mul,
              Real.rpow_neg (by positivity), inv_inv]
          rw [h2r_eq, one_div]
          exact (inv_lt_inv₀ (by positivity) him_pos).mpr h2r |>.le
        rw [hmin_eq]
        have : 0 ≤ C_env * Real.exp (tipH ζ₀) := by positivity
        nlinarith [hbd1]
    · have hnorm_pos : 0 < ‖ζ₀‖ := by linarith
      have hlog_bd3 : Real.log ‖tipRescale c' test ζ₀‖ ≤
          tipH ζ₀ + Real.log C_env - Real.log ‖ζ₀‖ := by
        have hlog4norm : -Real.log (‖ζ₀‖ / 4) = Real.log 4 - Real.log ‖ζ₀‖ := by
          rw [Real.log_div hnorm_pos.ne' (by norm_num)]; ring
        have hC_log : Real.log C_env = 3 * KTip / 4 + |C₁| + Real.log 4 + 4 / π + 1 := Real.log_exp _
        have hpi_nn : 0 ≤ 4 / π := by positivity
        dsimp [M_const] at hsub
        linarith [havg.2.2.2 harg hnorm8]
      have hexp := Real.exp_le_exp.mpr hlog_bd3
      rw [Real.exp_log (norm_pos_iff.mpr hzero), sub_eq_add_neg, Real.exp_add, Real.exp_add,
        Real.exp_log hCenv_pos, Real.exp_neg, Real.exp_log hnorm_pos] at hexp
      calc ‖tipRescale c' test ζ₀‖
          ≤ Real.exp (tipH ζ₀) * C_env * ‖ζ₀‖⁻¹ := hexp
        _ = C_env * Real.exp (tipH ζ₀) / ‖ζ₀‖ := by rw [div_eq_mul_inv]; ring

/-! ### Section 2: Montel exhaustion on `ℂ` via diagonal subsequence -/

/-- General Montel exhaustion on `ℂ`: if `F : ℕ → ℂ → ℂ` is eventually holomorphic and uniformly
bounded on every `ball 0 R`, then a subsequence converges locally uniformly on `ℂ` to an entire
function `Ψ`. -/
theorem montel_exhaustion_entire (F : ℕ → ℂ → ℂ)
    (hhol : ∀ R : ℝ, 0 ≤ R → ∀ᶠ n in atTop, DifferentiableOn ℂ (F n) (ball 0 R))
    (hbdd : ∀ R : ℝ, 0 ≤ R → ∃ M : ℝ, ∀ᶠ n in atTop, ∀ z ∈ ball 0 R, ‖F n z‖ ≤ M) :
    ∃ (φ : ℕ → ℕ) (Ψ : ℂ → ℂ),
      StrictMono φ ∧ Differentiable ℂ Ψ ∧
      TendstoLocallyUniformlyOn (fun k => F (φ k)) Ψ atTop univ := by
  classical
  have hstep : ∀ (k : ℕ) (ψ : ℕ → ℕ), StrictMono ψ →
      ∃ χ : ℕ → ℕ, StrictMono χ ∧ ∃ f : ℂ → ℂ,
        DifferentiableOn ℂ f (ball 0 (k + 1 : ℝ)) ∧
        TendstoLocallyUniformlyOn (fun m => F (ψ (χ m))) f atTop (ball 0 (k + 1 : ℝ)) := by
    intro k ψ hψ
    obtain ⟨M, hM⟩ := hbdd (k + 1 : ℝ) (by positivity)
    obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp (hhol (k + 1 : ℝ) (by positivity))
    obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp hM
    let N : ℕ := max N₁ N₂
    let G : ℕ → ℂ → ℂ := fun m => F (ψ (m + N))
    have hGd : ∀ m, DifferentiableOn ℂ (G m) (ball 0 (k + 1 : ℝ)) := fun m =>
      hN₁ _ ((le_trans (le_max_left _ _) (Nat.le_add_left N m)).trans (hψ.id_le _))
    have hGb : FormalResearch.Montel.LocallyBounded G (ball 0 (k + 1 : ℝ)) := fun K hK _ =>
      ⟨M, fun m z hz => hN₂ _ ((le_trans (le_max_right _ _) (Nat.le_add_left N m)).trans (hψ.id_le _))
        z (hK hz)⟩
    obtain ⟨χ₀, hχ₀, f, hf, hlim⟩ := FormalResearch.Montel.montel isOpen_ball hGd hGb
    refine ⟨fun m => χ₀ m + N, fun a b hab => Nat.add_lt_add_right (hχ₀ hab) N, f, hf, hlim⟩
  let build : (k : ℕ) →
      { p : (ℕ → ℕ) × (ℂ → ℂ) //
        StrictMono p.1 ∧ DifferentiableOn ℂ p.2 (ball 0 (k + 1 : ℝ)) ∧
        TendstoLocallyUniformlyOn (fun m => F (p.1 m)) p.2 atTop (ball 0 (k + 1 : ℝ)) } :=
    Nat.rec
      (by
        let w := hstep 0 id strictMono_id
        exact ⟨⟨w.choose, w.choose_spec.2.choose⟩,
          w.choose_spec.1, w.choose_spec.2.choose_spec.1, w.choose_spec.2.choose_spec.2⟩)
      (fun k prev => by
        let w := hstep (k + 1) prev.1.1 prev.2.1
        have hcomp : StrictMono (prev.1.1 ∘ w.choose) := prev.2.1.comp w.choose_spec.1
        exact ⟨⟨prev.1.1 ∘ w.choose, w.choose_spec.2.choose⟩,
          hcomp, w.choose_spec.2.choose_spec.1, w.choose_spec.2.choose_spec.2⟩)
  have hex_sub : ∀ k : ℕ, ∃ χ : ℕ → ℕ, StrictMono χ ∧
      (build (k + 1)).1.1 = (build k).1.1 ∘ χ := fun k =>
    ⟨(hstep (k + 1) (build k).1.1 (build k).2.1).choose,
      (hstep (k + 1) (build k).1.1 (build k).2.1).choose_spec.1, rfl⟩
  have hchain : ∀ (k d m : ℕ), ∃ r : ℕ, m ≤ r ∧ (build (k + d)).1.1 m = (build k).1.1 r := by
    intro k d
    induction d with
    | zero => intro m; exact ⟨m, le_rfl, rfl⟩
    | succ d ih =>
        intro m
        obtain ⟨χ, hχ, heq⟩ := hex_sub (k + d)
        rw [show k + (d + 1) = (k + d) + 1 by omega, heq, Function.comp_apply]
        obtain ⟨r, hr, hrm⟩ := ih (χ m)
        exact ⟨r, (hχ.id_le m).trans hr, hrm⟩
  let φ : ℕ → ℕ := fun k => (build k).1.1 k
  have hφ_strict : StrictMono φ := by
    refine strictMono_nat_of_lt_succ fun k => ?_
    obtain ⟨χ, hχ, heq⟩ := hex_sub k
    have hlt : k < χ (k + 1) := lt_of_lt_of_le (Nat.lt_succ_self k) (hχ.id_le (k + 1))
    dsimp [φ]
    rw [heq, Function.comp_apply]
    exact (build k).2.1 hlt
  have hcompat : ∀ (k₁ k₂ : ℕ) {z : ℂ}, z ∈ ball 0 (k₁ + 1 : ℝ) → k₁ ≤ k₂ →
      (build k₁).1.2 z = (build k₂).1.2 z := by
    intro k₁ k₂ z hz hle
    let d := k₂ - k₁
    have hk₂ : k₁ + d = k₂ := Nat.add_sub_of_le hle
    have hz₂ : z ∈ ball 0 (k₂ + 1 : ℝ) :=
      ball_subset_ball (by gcongr) hz
    have hlim₁ : Tendsto (fun m => F ((build k₁).1.1 m) z) atTop (nhds ((build k₁).1.2 z)) :=
      (build k₁).2.2.2.tendsto_at hz
    have hlim₂ : Tendsto (fun m => F ((build k₂).1.1 m) z) atTop (nhds ((build k₂).1.2 z)) :=
      (build k₂).2.2.2.tendsto_at hz₂
    have hsub_lim : Tendsto (fun m => F ((build k₂).1.1 m) z) atTop (nhds ((build k₁).1.2 z)) := by
      rw [Metric.tendsto_atTop] at hlim₁ ⊢
      intro ε hε
      obtain ⟨N, hN⟩ := hlim₁ ε hε
      refine ⟨N, fun m hm => ?_⟩
      obtain ⟨r, hr, heqr⟩ := hchain k₁ d m
      rw [← hk₂, heqr]
      exact hN r (hm.trans hr)
    exact tendsto_nhds_unique hsub_lim hlim₂
  let Ψ : ℂ → ℂ := fun z => (build (Nat.ceil ‖z‖)).1.2 z
  have hΨ_eq : ∀ k : ℕ, ∀ z ∈ ball 0 (k + 1 : ℝ), Ψ z = (build k).1.2 z := by
    intro k z hz
    let kz : ℕ := Nat.ceil ‖z‖
    have hzk : z ∈ ball 0 (kz + 1 : ℝ) := by
      rw [mem_ball, dist_zero_right]
      exact (Nat.le_ceil ‖z‖).trans_lt (lt_add_one _)
    dsimp [Ψ]
    rcases le_total kz k with hk | hk
    · exact hcompat kz k hzk hk
    · exact (hcompat k kz hz hk).symm
  have hTLU : TendstoLocallyUniformlyOn (fun k => F (φ k)) Ψ atTop univ := by
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ]
    intro K _ hK
    obtain ⟨R, hKR⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
    let k : ℕ := Nat.ceil (max R 0) + 1
    have hK_ball : K ⊆ ball (0 : ℂ) (k + 1 : ℝ) := fun z hz => by
      rw [mem_ball, dist_zero_right]
      have h1 : ‖z‖ ≤ max R 0 := (mem_closedBall_zero_iff.mp (hKR hz)).trans (le_max_left _ _)
      have h2 : max R 0 ≤ (Nat.ceil (max R 0) : ℝ) := Nat.le_ceil _
      dsimp [k]; push_cast; linarith
    have hunif_k := ((tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_ball).mp
      (build k).2.2.2) K hK_ball hK
    rw [Metric.tendstoUniformlyOn_iff] at hunif_k ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hunif_k ε hε)
    rw [eventually_atTop]
    refine ⟨max k N, fun m hm z hz => ?_⟩
    have hkm : k ≤ m := (le_max_left _ _).trans hm
    have hNm : N ≤ m := (le_max_right _ _).trans hm
    obtain ⟨r, hr, heqr⟩ := hchain k (m - k) m
    rw [Nat.add_sub_of_le hkm] at heqr
    have heq_φ : φ m = (build k).1.1 r := heqr
    rw [hΨ_eq k z (hK_ball hz), heq_φ]
    exact hN r (hNm.trans hr) z hz
  have hΨ_diff : Differentiable ℂ Ψ := by
    intro z
    let k : ℕ := Nat.ceil ‖z‖
    have hzk : z ∈ ball (0 : ℂ) (k + 1 : ℝ) := by
      rw [mem_ball, dist_zero_right]
      exact (Nat.le_ceil ‖z‖).trans_lt (lt_add_one _)
    have hd : DifferentiableAt ℂ ((build k).1.2) z :=
      ((build k).2.2.1).differentiableAt (isOpen_ball.mem_nhds hzk)
    refine hd.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_ball.mem_nhds hzk] with w hw
    exact hΨ_eq k w hw
  exact ⟨φ, Ψ, hφ_strict, hΨ_diff, hTLU⟩

/-! ### Section 3: Left-tail control (`blowup_left_tail_bound`) -/

private lemma integral_Ioc_tipRescale_eq {inp : StripBootstrapInputs} {c' : ℝ} (hc' : 0 < c')
    (test : BlowupTest inp c') {R : ℝ} (hεR : tipEps c' * R < xiStar) :
    ∫ s in Ioc (tipSMin c') (-R), ‖tipRescale c' test (s : ℂ)‖ =
      (test.M)⁻¹ * ∫ t in Ioc 0 (c' * (xiStar - tipEps c' * R) ^ 2 / 3), |test.g t| * test.V t := by
  have hε_pos := tipEps_pos hc'
  have hsMin_lt : tipSMin c' < -R := by
    rw [tipSMin_eq_neg_div_tipEps hc', div_lt_iff₀ hε_pos]
    linarith
  have hxi_sub_pos : 0 < xiStar - tipEps c' * R := sub_pos.mpr hεR
  have him : tipTReal c' '' Ioc (tipSMin c') (-R) =
      Ioc 0 (c' * (xiStar - tipEps c' * R) ^ 2 / 3) := by
    ext t
    constructor
    · rintro ⟨s, ⟨hs1, hs2⟩, rfl⟩
      have hbs_pos : 0 < tipBReal c' s := (tipBReal_pos_iff hc').mpr hs1
      have hbs_le : tipBReal c' s ≤ xiStar - tipEps c' * R := by
        unfold tipBReal; linarith [mul_le_mul_of_nonneg_left hs2 hε_pos.le]
      have ht_pos : 0 < tipTReal c' s := by unfold tipTReal; positivity
      have ht_le : tipTReal c' s ≤ c' * (xiStar - tipEps c' * R) ^ 2 / 3 := by
        unfold tipTReal
        have : tipBReal c' s ^ 2 ≤ (xiStar - tipEps c' * R) ^ 2 := by nlinarith
        gcongr
      exact ⟨ht_pos, ht_le⟩
    · rintro ⟨ht_pos, ht_le⟩
      let s : ℝ := (Real.sqrt (3 * t / c') - xiStar) / tipEps c'
      have hbs : tipBReal c' s = Real.sqrt (3 * t / c') := by
        unfold tipBReal
        have hm : tipEps c' * s = Real.sqrt (3 * t / c') - xiStar := by
          dsimp [s]; rw [mul_div_cancel₀ _ hε_pos.ne']
        linarith
      have hs1 : tipSMin c' < s := by
        rw [← tipBReal_pos_iff hc', hbs]; positivity
      have hs2 : s ≤ -R := by
        have h3t : 3 * t / c' ≤ (xiStar - tipEps c' * R) ^ 2 := by
          rw [div_le_iff₀ hc']; linarith
        have hsqrt_le : Real.sqrt (3 * t / c') ≤ xiStar - tipEps c' * R := by
          rw [← Real.sqrt_sq hxi_sub_pos.le]; exact Real.sqrt_le_sqrt h3t
        have h1 : tipEps c' * s ≤ tipEps c' * (-R) := by
          unfold tipBReal at hbs
          linarith [show tipEps c' * (-R) = -(tipEps c' * R) by ring]
        exact le_of_mul_le_mul_left h1 hε_pos
      refine ⟨s, ⟨hs1, hs2⟩, ?_⟩
      unfold tipTReal
      rw [hbs, Real.sq_sqrt (by positivity)]
      field_simp [hc'.ne']
  have hcov := integral_image_eq_integral_abs_deriv_smul (s := Ioc (tipSMin c') (-R))
    measurableSet_Ioc
    (fun s _ => (tipTReal_deriv (c' := c') (s := s)).hasDerivWithinAt)
    ((tipTReal_injOn hc').mono Ioc_subset_Ioi_self)
    (fun t => (test.M)⁻¹ * (|test.g t| * test.V t))
  rw [him] at hcov
  have heq : EqOn (fun s : ℝ => ‖tipRescale c' test (s : ℂ)‖)
      (fun s => |tipEps c' * (2 * c' / 3) * tipBReal c' s| •
        ((test.M)⁻¹ * (|test.g (tipTReal c' s)| * test.V (tipTReal c' s))))
      (Ioc (tipSMin c') (-R)) := fun s hs => by
    have hbs : 0 < tipBReal c' s := (tipBReal_pos_iff hc').mpr hs.1
    have hts : 0 < tipTReal c' s := by unfold tipTReal; positivity
    have hder_nn : 0 ≤ tipEps c' * (2 * c' / 3) * tipBReal c' s :=
      mul_nonneg (mul_nonneg hε_pos.le (by positivity)) hbs.le
    have hnum_nn : 0 ≤ tipEps c' * (2 * c' / 3) * tipBReal c' s * test.V (tipTReal c' s) :=
      mul_nonneg hder_nn (test.hV_pos _ hts).le
    dsimp only
    rw [tipRescale_real_on_real, Complex.norm_real, Real.norm_eq_abs, smul_eq_mul,
      abs_of_nonneg hder_nn, abs_div, abs_of_pos test.hM_pos, abs_mul,
      abs_of_nonneg hnum_nn]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioc heq, ← hcov, integral_const_mul]

/-- Uniform left-tail estimate (`blowup_limit.tex`, §4 "Tail control" & Proposition T (v)):
there exists `η : ℝ → ℝ` with `η R → 0` as `R → ∞` such that for all `1 ≤ R`, eventually in
`c' → ∞`, `∫ s in Ioc (tipSMin c') (-R), ‖tipRescale c' test (s : ℂ)‖ ≤ η R` uniformly
across all `test : BlowupTest inp c'`. -/
theorem blowup_left_tail_bound (inp : StripBootstrapInputs) :
    ∃ η : ℝ → ℝ, Tendsto η atTop (nhds 0) ∧
      ∀ R : ℝ, 1 ≤ R → ∀ᶠ c' : ℝ in atTop,
        ∀ test : BlowupTest inp c',
          ∫ s in Ioc (tipSMin c') (-R), ‖tipRescale c' test (s : ℂ)‖ ≤ η R := by
  obtain ⟨C_M1, C_M2, hCM1_nn, hpropM⟩ := proposition_M inp.pj.rs (C_PJ := inp.pj.C_PJ) inp.pj.hc_PJ
  let C_pref : ℝ := 2 * inp.pj.C_K * Real.exp C_M2
  have hC_pref_pos : 0 < C_pref := mul_pos (mul_pos two_pos inp.pj.hC_K) (Real.exp_pos C_M2)
  let δ₀ : ℝ := xiStar - 0.05
  have hδ₀_pos : 0 < δ₀ := sub_pos.mpr xiStar_gt_005
  refine ⟨fun R => (C_pref + 1) * Real.exp (-R), ?_, fun R hR => ?_⟩
  · have := (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).const_mul (C_pref + 1)
    simpa using this
  have hc_log_bound : ∀ {c' : ℝ}, 1 ≤ c' → (max 1 (6 * C_M1)) ^ 6 ≤ c' →
      C_M1 * c' ^ (-(1 / 3 : ℝ)) * Real.log c' ≤ 1 := fun {c'} hc'1 hc'_log => by
    have hc'_pos : 0 < c' := by linarith
    have hc'_16 : max 1 (6 * C_M1) ≤ c' ^ ((1 : ℝ) / 6) := by
      have := Real.rpow_le_rpow (by positivity) hc'_log (by norm_num : (0 : ℝ) ≤ 1 / 6)
      rwa [← Real.rpow_natCast (max 1 (6 * C_M1)) 6, ← Real.rpow_mul (by positivity),
        show ((6 : ℕ) : ℝ) * (1 / 6) = 1 by norm_num, Real.rpow_one] at this
    have hlog_le : Real.log c' ≤ 6 * c' ^ ((1 : ℝ) / 6) := by
      have h1 := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hc'_pos (1 / 6))
      rw [Real.log_rpow hc'_pos] at h1; linarith
    have hpow_comb : c' ^ (-(1 / 3 : ℝ)) * c' ^ ((1 : ℝ) / 6) = (c' ^ ((1 : ℝ) / 6))⁻¹ := by
      rw [← Real.rpow_add hc'_pos, ← Real.rpow_neg hc'_pos.le]; norm_num
    calc C_M1 * c' ^ (-(1 / 3 : ℝ)) * Real.log c'
        ≤ C_M1 * c' ^ (-(1 / 3 : ℝ)) * (6 * c' ^ ((1 : ℝ) / 6)) := by gcongr
      _ = (6 * C_M1) * (c' ^ ((1 : ℝ) / 6))⁻¹ := by rw [← hpow_comb]; ring
      _ ≤ (c' ^ ((1 : ℝ) / 6)) * (c' ^ ((1 : ℝ) / 6))⁻¹ := by
          gcongr; exact (le_max_right 1 (6 * C_M1)).trans hc'_16
      _ = 1 := mul_inv_cancel₀ (Real.rpow_pos_of_pos hc'_pos _).ne'
  have hdeep_ev : ∀ᶠ c' : ℝ in atTop,
      inp.fg.C_deep * Real.exp (-inp.fg.κ_deep * c') ≤ Real.exp (-R) := by
    have htend : Tendsto (fun c' : ℝ => inp.fg.C_deep * Real.exp (-inp.fg.κ_deep * c'))
        atTop (nhds 0) := by
      have harg : Tendsto (fun c' : ℝ => -inp.fg.κ_deep * c') atTop atBot := by
        simpa [neg_mul] using tendsto_neg_atBot_iff.mpr
          (tendsto_id.const_mul_atTop inp.fg.hκ_deep)
      simpa using (Real.tendsto_exp_atBot.comp harg).const_mul inp.fg.C_deep
    exact htend.eventually (eventually_le_nhds (Real.exp_pos (-R)))
  have hεR_ev : ∀ᶠ c' : ℝ in atTop, tipEps c' * R < δ₀ := by
    have h0 : Tendsto (fun c' : ℝ => tipEps c' * R) atTop (nhds 0) := by
      simpa [tipEps] using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).mul_const R
    exact h0.eventually (eventually_lt_nhds hδ₀_pos)
  filter_upwards [eventually_ge_atTop (max 1 (max inp.pj.c_PJ inp.fg.c_deep)),
    eventually_ge_atTop ((max 1 (6 * C_M1)) ^ 6),
    hdeep_ev, hεR_ev] with c' hc'_base hc'_log hdeep_le hεR_lt
  have hc'_ge1 : 1 ≤ c' := (le_max_left _ _).trans hc'_base
  have hc'_pos : 0 < c' := by linarith
  have hc'_PJ : inp.pj.c_PJ ≤ c' := ((le_max_left _ _).trans (le_max_right _ _)).trans hc'_base
  have hc'_deep : inp.fg.c_deep ≤ c' := ((le_max_right _ _).trans (le_max_right _ _)).trans hc'_base
  have hε_pos : 0 < tipEps c' := tipEps_pos hc'_pos
  intro test
  have hεR_xi : tipEps c' * R < xiStar := by dsimp [δ₀] at hεR_lt; linarith
  rw [integral_Ioc_tipRescale_eq hc'_pos test hεR_xi]
  let t₀ : ℝ := c' * (0.05 : ℝ) ^ 2 / 3
  let t_R : ℝ := c' * (xiStar - tipEps c' * R) ^ 2 / 3
  have ht₀_pos : 0 < t₀ := by positivity
  have hx_05_lt : (0.05 : ℝ) < xiStar - tipEps c' * R := by dsimp [δ₀] at hεR_lt; linarith
  have ht₀_le_tR : t₀ ≤ t_R := by
    dsimp [t₀, t_R]
    have : (0.05 : ℝ) ^ 2 ≤ (xiStar - tipEps c' * R) ^ 2 := by nlinarith
    gcongr
  have hint_tR : IntegrableOn (fun t => |test.g t| * test.V t) (Ioc 0 t_R) :=
    test.hM_int.mono_set Ioc_subset_Ioi_self
  have hsplit : ∫ t in Ioc 0 t_R, |test.g t| * test.V t =
      (∫ t in Ioc 0 t₀, |test.g t| * test.V t) + (∫ t in Ioc t₀ t_R, |test.g t| * test.V t) := by
    rw [← Ioc_union_Ioc_eq_Ioc ht₀_pos.le ht₀_le_tR]
    exact setIntegral_union (Ioc_disjoint_Ioc_of_le (le_rfl : t₀ ≤ t₀)) measurableSet_Ioc
      (hint_tR.mono_set (Ioc_subset_Ioc_right ht₀_le_tR))
      (hint_tR.mono_set (Ioc_subset_Ioc_left ht₀_pos.le))
  have hdeep_bd : (test.M)⁻¹ * ∫ t in Ioc 0 t₀, |test.g t| * test.V t ≤ Real.exp (-R) := by
    rw [← intervalIntegral.integral_of_le ht₀_pos.le]
    have h1 := (test.hDeepLobe hc'_deep).trans
      (mul_le_mul_of_nonneg_right hdeep_le test.hM_pos.le)
    calc (test.M)⁻¹ * ∫ t in (0 : ℝ)..t₀, |test.g t| * test.V t
        ≤ (test.M)⁻¹ * (Real.exp (-R) * test.M) :=
          mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr test.hM_pos.le)
      _ = Real.exp (-R) := by field_simp [test.hM_pos.ne']
  have hairy_bd : ∫ t in Ioc t₀ t_R, |test.g t| * test.V t ≤
      C_pref * Real.exp (-R) * test.M := by
    rw [← intervalIntegral.integral_of_le ht₀_le_tR]
    have hprop := hpropM hc'_PJ test.hM_pos test.hPJ_real
    have hlog_c := hc_log_bound hc'_ge1 hc'_log
    -- Change variables `t = c' * x^2 / 3` (`x ∈ [0.05, xiStar - ε R]`), then `δ = xiStar - x`, `λ = δ / ε`.
    let φ : ℝ → ℝ := fun x => c' * x ^ 2 / 3
    let φ' : ℝ → ℝ := fun x => (2 / 3 : ℝ) * c' * x
    have hcov := intervalIntegral.integral_comp_mul_deriv'
      (fun x _ => (((hasDerivAt_pow 2 x).const_mul c').div_const 3).congr_deriv (by dsimp [φ']; ring))
      (by dsimp [φ']; fun_prop : ContinuousOn φ' (uIcc (0.05 : ℝ) (xiStar - tipEps c' * R)))
      (((test.hg_cont.abs).mul test.hV_cont).mono
        (by rintro t ⟨x, _, rfl⟩; exact mem_Ici.mpr (by dsimp [φ]; positivity)))
    have hφ_eq : ∫ t in t₀..t_R, |test.g t| * test.V t =
        ∫ x in (0.05 : ℝ)..(xiStar - tipEps c' * R),
          |test.g (c' * x ^ 2 / 3)| * test.V (c' * x ^ 2 / 3) * ((2 / 3 : ℝ) * c' * x) := by
      simpa [φ, φ', t₀, t_R] using hcov.symm
    have hint_x : IntervalIntegrable
        (fun x => |test.g (c' * x ^ 2 / 3)| * test.V (c' * x ^ 2 / 3) * ((2 / 3 : ℝ) * c' * x))
        volume 0.05 (xiStar - tipEps c' * R) :=
      ((((test.hg_cont.comp (by fun_prop) fun x _ => mem_Ici.mpr (by positivity)).abs).mul
        (test.hV_cont.comp (by fun_prop) fun x _ => mem_Ici.mpr (by positivity))).mul
        (by fun_prop)).intervalIntegrable_of_Icc hx_05_lt.le
    let F_δ : ℝ → ℝ := fun δ =>
      C_pref * test.M * δ⁻¹ *
        Real.exp (-2.228 * c' * δ ^ ((3 : ℝ) / 2) + C_M1 * Real.sqrt δ * Real.log c')
    let F_x : ℝ → ℝ := fun x => F_δ (xiStar - x)
    let δ_R : ℝ := tipEps c' * R
    have hδ_R_pos : 0 < δ_R := mul_pos hε_pos (by linarith)
    have hδ_R_lt : δ_R < δ₀ := hεR_lt
    have hint_Fδ : IntervalIntegrable F_δ volume δ_R δ₀ := by
      have hcont1 : ContinuousOn (fun δ : ℝ => C_pref * test.M * δ⁻¹) (Icc δ_R δ₀) :=
        continuousOn_const.mul (continuousOn_id.inv₀ fun δ hδ => (lt_of_lt_of_le hδ_R_pos hδ.1).ne')
      have hcont2 : ContinuousOn (fun δ : ℝ => -2.228 * c' * δ ^ ((3 : ℝ) / 2)) (Icc δ_R δ₀) :=
        continuousOn_const.mul
          (continuousOn_id.rpow_const fun δ hδ => Or.inl (lt_of_lt_of_le hδ_R_pos hδ.1).ne')
      have hcont3 : ContinuousOn (fun δ : ℝ => C_M1 * Real.sqrt δ * Real.log c') (Icc δ_R δ₀) :=
        ((continuous_const.mul Real.continuous_sqrt).mul continuous_const).continuousOn
      exact (hcont1.mul (hcont2.add hcont3).rexp).intervalIntegrable_of_Icc hδ_R_lt.le
    have hsub_δ : ∫ x in (0.05 : ℝ)..(xiStar - δ_R), F_x x = ∫ δ in δ_R..δ₀, F_δ δ := by
      change ∫ x in (0.05 : ℝ)..(xiStar - δ_R), F_δ (xiStar - x) = ∫ δ in δ_R..δ₀, F_δ δ
      rw [intervalIntegral.integral_comp_sub_left F_δ xiStar, sub_sub_cancel,
        show xiStar - (0.05 : ℝ) = δ₀ by rfl]
    have hint_Fx : IntervalIntegrable F_x volume 0.05 (xiStar - δ_R) := by
      have h := (hint_Fδ.comp_sub_left xiStar).symm
      dsimp [δ₀] at h
      rw [sub_sub_cancel] at h
      exact h
    have hmono_x : ∫ x in (0.05 : ℝ)..(xiStar - δ_R),
        |test.g (c' * x ^ 2 / 3)| * test.V (c' * x ^ 2 / 3) * ((2 / 3 : ℝ) * c' * x) ≤
        ∫ x in (0.05 : ℝ)..(xiStar - δ_R), F_x x := by
      refine intervalIntegral.integral_mono_on hx_05_lt.le hint_x hint_Fx fun x hx => ?_
      have hx_Ico : x ∈ Ico 0 xiStar := ⟨by linarith [hx.1], by dsimp [δ_R] at hx; linarith [hx.2]⟩
      have hx_Icc : x ∈ Icc (0.05 : ℝ) xiStar := ⟨hx.1, by dsimp [δ_R] at hx; linarith [hx.2]⟩
      have hδ_pos : 0 < xiStar - x := sub_pos.mpr hx_Ico.2
      have hG_ub : |test.g (c' * x ^ 2 / 3)| ≤
          test.M * c' ^ (-(1 / 2 : ℝ)) * (1 / (xiStar - x)) *
            Real.exp (c' * inp.pj.U x + C_M1 * Real.sqrt (xiStar - x) * Real.log c' + C_M2) := by
        by_cases hg0 : test.g (c' * x ^ 2 / 3) = 0
        · rw [hg0, abs_zero]; positivity [test.hM_pos]
        · have hexp := Real.exp_le_exp.mpr (hprop x hx_Ico hg0)
          rw [Real.exp_log (abs_pos.mpr hg0)] at hexp
          refine hexp.trans_eq ?_
          rw [show c' * inp.pj.U x + Real.log test.M - (1 / 2 : ℝ) * Real.log c' +
                C_M1 * Real.sqrt (xiStar - x) * Real.log c' +
                Real.log (1 / (xiStar - x)) + C_M2 =
              (Real.log test.M + Real.log c' * (-(1 / 2 : ℝ)) + Real.log (1 / (xiStar - x))) +
                (c' * inp.pj.U x + C_M1 * Real.sqrt (xiStar - x) * Real.log c' + C_M2) by ring,
            Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_log test.hM_pos,
            Real.exp_log (one_div_pos.mpr hδ_pos), ← Real.rpow_def_of_pos hc'_pos]
      have hV_ub : test.V (c' * x ^ 2 / 3) ≤
          2 * inp.pj.C_K * Real.exp (c' * ((2 * π / 3) * x)) * c' ^ (-(1 / 2 : ℝ)) := by
        calc test.V (c' * x ^ 2 / 3) ≤ 2 * test.K_a (c' * x ^ 2 / 3) := test.hV_le_two_Ka x hx_Icc
          _ ≤ 2 * (inp.pj.C_K * Real.exp (c' * ((2 * π / 3) * x)) / Real.sqrt c') := by
              gcongr; exact test.hKa_ub x hx_Icc
          _ = 2 * inp.pj.C_K * Real.exp (c' * ((2 * π / 3) * x)) * c' ^ (-(1 / 2 : ℝ)) := by
              rw [Real.sqrt_eq_rpow, div_eq_mul_inv, ← Real.rpow_neg hc'_pos.le]; ring
      have hdt_nn : 0 ≤ (2 / 3 : ℝ) * c' * x :=
        mul_nonneg (mul_nonneg (by norm_num) hc'_pos.le) (by linarith [hx.1])
      have hdt_ub : (2 / 3 : ℝ) * c' * x ≤ c' := by
        have hx1 : x ≤ 1 := by linarith [hx_Ico.2, xiStar_lt_one]
        calc (2 / 3 : ℝ) * c' * x ≤ (2 / 3 : ℝ) * c' * 1 := by gcongr
          _ ≤ c' := by linarith
      have hpow_cancel : c' ^ (-(1 / 2 : ℝ)) * c' ^ (-(1 / 2 : ℝ)) * c' = 1 := by
        rw [← Real.rpow_add hc'_pos]; norm_num
        rw [Real.rpow_neg_one, inv_mul_cancel₀ hc'_pos.ne']
      have hdef_ub : c' * (inp.pj.U x + (2 * π / 3) * x) ≤
          -2.228 * c' * (xiStar - x) ^ ((3 : ℝ) / 2) :=
        (mul_le_mul_of_nonneg_left
          ((inp.pj.g_deficit x hx_Ico).trans (neg_le_neg (slitDeficit_ge hδ_pos.le (by linarith [hx.1]))))
          hc'_pos.le).trans_eq (by ring)
      have hV_rhs_nn : 0 ≤ 2 * inp.pj.C_K * Real.exp (c' * ((2 * π / 3) * x)) * c' ^ (-(1 / 2 : ℝ)) :=
        mul_nonneg (mul_nonneg (mul_nonneg two_pos.le inp.pj.hC_K.le) (Real.exp_pos _).le)
          (Real.rpow_nonneg hc'_pos.le _)
      have hG_nn : 0 ≤ test.M * c' ^ (-(1 / 2 : ℝ)) * (1 / (xiStar - x)) *
          Real.exp (c' * inp.pj.U x + C_M1 * Real.sqrt (xiStar - x) * Real.log c' + C_M2) :=
        by positivity [test.hM_pos]
      have hGV := mul_le_mul hG_ub hV_ub (test.hV_nonneg _ (by positivity)) hG_nn
      have hGdt := mul_le_mul hGV hdt_ub hdt_nn (mul_nonneg hG_nn hV_rhs_nn)
      have hprod_eq : (test.M * c' ^ (-(1 / 2 : ℝ)) * (1 / (xiStar - x)) *
            Real.exp (c' * inp.pj.U x + C_M1 * Real.sqrt (xiStar - x) * Real.log c' + C_M2)) *
            (2 * inp.pj.C_K * Real.exp (c' * ((2 * π / 3) * x)) * c' ^ (-(1 / 2 : ℝ))) * c' =
          C_pref * test.M * (xiStar - x)⁻¹ *
            Real.exp (c' * (inp.pj.U x + (2 * π / 3) * x) +
              C_M1 * Real.sqrt (xiStar - x) * Real.log c') := by
        rw [show c' * inp.pj.U x + C_M1 * Real.sqrt (xiStar - x) * Real.log c' + C_M2 =
            (c' * inp.pj.U x + C_M1 * Real.sqrt (xiStar - x) * Real.log c') + C_M2 by ring]
        calc (test.M * c' ^ (-(1 / 2 : ℝ)) * (1 / (xiStar - x)) *
              Real.exp ((c' * inp.pj.U x + C_M1 * Real.sqrt (xiStar - x) * Real.log c') + C_M2)) *
              (2 * inp.pj.C_K * Real.exp (c' * ((2 * π / 3) * x)) * c' ^ (-(1 / 2 : ℝ))) * c'
            = (2 * inp.pj.C_K * Real.exp C_M2) * test.M * (xiStar - x)⁻¹ *
                (c' ^ (-(1 / 2 : ℝ)) * c' ^ (-(1 / 2 : ℝ)) * c') *
                (Real.exp (c' * inp.pj.U x + C_M1 * Real.sqrt (xiStar - x) * Real.log c') *
                  Real.exp (c' * ((2 * π / 3) * x))) := by
                rw [Real.exp_add]; ring
          _ = C_pref * test.M * (xiStar - x)⁻¹ *
                Real.exp (c' * (inp.pj.U x + (2 * π / 3) * x) +
                  C_M1 * Real.sqrt (xiStar - x) * Real.log c') := by
              rw [hpow_cancel, mul_one, ← Real.exp_add]; congr 2; ring
      refine hGdt.trans (hprod_eq.le.trans ?_)
      have hpref_nn : 0 ≤ C_pref * test.M * (xiStar - x)⁻¹ := by positivity [test.hM_pos]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by gcongr)) hpref_nn
    let s : ℝ := tipEps c'
    let B_lam : ℝ := δ₀ / s
    have hR_le_B : R ≤ B_lam := by
      dsimp [B_lam, s]; rw [le_div_iff₀ hε_pos]; linarith [hεR_lt]
    have hscale_lam : ∫ δ in δ_R..δ₀, F_δ δ = s * ∫ l in R..B_lam, F_δ (s * l) := by
      have h := intervalIntegral.integral_comp_mul_left F_δ hε_pos.ne' (a := R) (b := B_lam)
      rw [show s * R = δ_R by rfl,
        show s * B_lam = δ₀ by dsimp [B_lam]; exact mul_div_cancel₀ _ hε_pos.ne'] at h
      rw [h, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hε_pos.ne', one_mul]
    have hint_sFδ : IntervalIntegrable (fun l => s * F_δ (s * l)) volume R B_lam := by
      have hcomp := hint_Fδ.comp_mul_left (c := s) enorm_ne_top enorm_ne_top
      rw [show δ_R / s = R by dsimp [δ_R, s]; exact mul_div_cancel_left₀ _ hε_pos.ne'] at hcomp
      exact hcomp.const_mul s
    have hmono_lam : ∫ l in R..B_lam, s * F_δ (s * l) ≤
        ∫ l in R..B_lam, C_pref * test.M * Real.exp (-l) := by
      refine intervalIntegral.integral_mono_on hR_le_B hint_sFδ
        ((Continuous.intervalIntegrable (by fun_prop) _ _).const_mul _) fun l hl => ?_
      have hl_ge1 : 1 ≤ l := hR.trans hl.1
      have hl_pos : 0 < l := zero_lt_one.trans_le hl_ge1
      have hcancel_1 : s * (s * l)⁻¹ = l⁻¹ := by
        rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ hε_pos.ne', one_mul]
      have hcancel_2 : c' * (s * l) ^ ((3 : ℝ) / 2) = l ^ ((3 : ℝ) / 2) := by
        rw [Real.mul_rpow hε_pos.le hl_pos.le]; dsimp [s, tipEps]
        rw [← Real.rpow_mul hc'_pos.le, show -(2 / 3 : ℝ) * (3 / 2) = -1 by norm_num,
          ← mul_assoc, Real.rpow_neg_one, mul_inv_cancel₀ hc'_pos.ne', one_mul]
      have hcancel_3 : Real.sqrt (s * l) = c' ^ (-(1 / 3 : ℝ)) * Real.sqrt l := by
        rw [Real.sqrt_mul hε_pos.le, Real.sqrt_eq_rpow]; dsimp [s, tipEps]
        rw [← Real.rpow_mul hc'_pos.le]; norm_num
      have hCM1_ub : C_M1 * Real.sqrt (s * l) * Real.log c' ≤ Real.sqrt l := by
        rw [hcancel_3]
        calc C_M1 * (c' ^ (-(1 / 3 : ℝ)) * Real.sqrt l) * Real.log c'
            = (C_M1 * c' ^ (-(1 / 3 : ℝ)) * Real.log c') * Real.sqrt l := by ring
          _ ≤ 1 * Real.sqrt l := by gcongr
          _ = Real.sqrt l := one_mul _
      have hsqrt_le_l : Real.sqrt l ≤ l := by
        calc Real.sqrt l ≤ Real.sqrt (l ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
          _ = l := Real.sqrt_sq hl_pos.le
      have hl_le_32 : l ≤ l ^ ((3 : ℝ) / 2) := by
        calc l = l ^ (1 : ℝ) := (Real.rpow_one l).symm
          _ ≤ l ^ ((3 : ℝ) / 2) := Real.rpow_le_rpow_of_exponent_le hl_ge1 (by norm_num)
      have hexp_arg : -2.228 * c' * (s * l) ^ ((3 : ℝ) / 2) +
          C_M1 * Real.sqrt (s * l) * Real.log c' ≤ -l := by
        rw [show -2.228 * c' * (s * l) ^ ((3 : ℝ) / 2) = -2.228 * (c' * (s * l) ^ ((3 : ℝ) / 2)) by ring,
          hcancel_2]
        linarith
      dsimp [F_δ]
      calc s * (C_pref * test.M * (s * l)⁻¹ *
              Real.exp (-2.228 * c' * (s * l) ^ ((3 : ℝ) / 2) +
                C_M1 * Real.sqrt (s * l) * Real.log c'))
          = C_pref * test.M * (s * (s * l)⁻¹) *
              Real.exp (-2.228 * c' * (s * l) ^ ((3 : ℝ) / 2) +
                C_M1 * Real.sqrt (s * l) * Real.log c') := by ring
        _ ≤ C_pref * test.M * 1 * Real.exp (-l) := by
            rw [hcancel_1]
            have hCM_nn : 0 ≤ C_pref * test.M := mul_nonneg hC_pref_pos.le test.hM_pos.le
            exact mul_le_mul (mul_le_mul_of_nonneg_left (inv_le_one_of_one_le₀ hl_ge1) hCM_nn)
              (Real.exp_le_exp.mpr hexp_arg) (Real.exp_pos _).le (mul_nonneg hCM_nn zero_le_one)
        _ = C_pref * test.M * Real.exp (-l) := by ring
    have hexp_int_ub : ∫ l in R..B_lam, Real.exp (-l) ≤ Real.exp (-R) := by
      have hd : ∀ l ∈ uIcc R B_lam, HasDerivAt (fun t : ℝ => -Real.exp (-t)) (Real.exp (-l)) l :=
        fun l _ => ((Real.hasDerivAt_exp _).comp l (hasDerivAt_neg l)).neg.congr_deriv (by ring)
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
        (Continuous.intervalIntegrable (by fun_prop) _ _)]
      linarith [Real.exp_pos (-B_lam)]
    calc ∫ t in t₀..t_R, |test.g t| * test.V t
        = ∫ x in (0.05 : ℝ)..(xiStar - δ_R),
            |test.g (c' * x ^ 2 / 3)| * test.V (c' * x ^ 2 / 3) * ((2 / 3 : ℝ) * c' * x) := hφ_eq
      _ ≤ ∫ x in (0.05 : ℝ)..(xiStar - δ_R), F_x x := hmono_x
      _ = ∫ δ in δ_R..δ₀, F_δ δ := hsub_δ
      _ = s * ∫ l in R..B_lam, F_δ (s * l) := hscale_lam
      _ = ∫ l in R..B_lam, s * F_δ (s * l) := (intervalIntegral.integral_const_mul _ _).symm
      _ ≤ ∫ l in R..B_lam, C_pref * test.M * Real.exp (-l) := hmono_lam
      _ = C_pref * test.M * ∫ l in R..B_lam, Real.exp (-l) :=
          intervalIntegral.integral_const_mul _ _
      _ ≤ C_pref * test.M * Real.exp (-R) :=
          mul_le_mul_of_nonneg_left hexp_int_ub (mul_nonneg hC_pref_pos.le test.hM_pos.le)
      _ = C_pref * Real.exp (-R) * test.M := by ring
  have hairy_scaled : (test.M)⁻¹ * ∫ t in Ioc t₀ t_R, |test.g t| * test.V t ≤
      C_pref * Real.exp (-R) := by
    calc (test.M)⁻¹ * ∫ t in Ioc t₀ t_R, |test.g t| * test.V t
        ≤ (test.M)⁻¹ * (C_pref * Real.exp (-R) * test.M) :=
          mul_le_mul_of_nonneg_left hairy_bd (inv_nonneg.mpr test.hM_pos.le)
      _ = C_pref * Real.exp (-R) := by field_simp [test.hM_pos.ne']
  rw [hsplit, mul_add]
  linarith

private lemma intervalIntegral_tendsto_of_tendstoUniformlyOn {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    {a b : ℝ} (hab : a ≤ b)
    (hunif : TendstoUniformlyOn f g atTop (Icc a b))
    (hf_int : ∀ᶠ k in atTop, IntervalIntegrable (f k) volume a b)
    (hg_cont : ContinuousOn g (Icc a b)) :
    Tendsto (fun k => ∫ s in a..b, f k s) atTop (nhds (∫ s in a..b, g s)) := by
  simp_rw [intervalIntegral.integral_of_le hab]
  have hbound_int : IntegrableOn (fun s => ‖g s‖ + 1) (Ioc a b) :=
    ((hg_cont.norm.add continuousOn_const).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hbound : ∀ᶠ k in atTop, ∀ᵐ s ∂volume.restrict (Ioc a b), ‖f k s‖ ≤ ‖g s‖ + 1 := by
    have hu := (Metric.tendstoUniformlyOn_iff.mp hunif) 1 zero_lt_one
    filter_upwards [hu] with k hk
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hd := hk s (Ioc_subset_Icc_self hs)
    rw [Real.dist_eq, abs_sub_comm] at hd
    calc ‖f k s‖ = |f k s| := Real.norm_eq_abs _
      _ ≤ |g s| + |f k s - g s| := by linarith [abs_sub_abs_le_abs_sub (f k s) (g s)]
      _ ≤ ‖g s‖ + 1 := by rw [Real.norm_eq_abs]; linarith
  have hlim : ∀ᵐ s ∂volume.restrict (Ioc a b), Tendsto (fun k => f k s) atTop (nhds (g s)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact hunif.tendsto_at (Ioc_subset_Icc_self hs)
  exact tendsto_integral_filter_of_dominated_convergence (fun s => ‖g s‖ + 1)
    (hf_int.mono fun _ hk => hk.1.aestronglyMeasurable) hbound hbound_int hlim

/-! ### Section 4: Proposition T (i)--(vi) (`blowup_limit.tex`, Proposition `bl:T`) -/

/-- Uniform Theorem A lower bound in tip-rescaled coordinates: `-C₀ ≤ tipS₁ c' test`
for all sufficiently large `c'` and all `test : BlowupTest inp c'`. -/
theorem tipS₁_theorem_A_lower (inp : StripBootstrapInputs) :
    ∃ C₀ c_A : ℝ, 0 < C₀ ∧ 1 ≤ c_A ∧
      ∀ {c' : ℝ}, c_A ≤ c' → ∀ test : BlowupTest inp c', -C₀ ≤ tipS₁ c' test := by
  obtain ⟨C_A, c_A, hCA_pos, hcA_ge1, hA⟩ := theorem_A inp.pj inp.fg
  let C₀ : ℝ := 3 * C_A / xiStar
  have hC₀_pos : 0 < C₀ := by positivity [xiStar_pos]
  refine ⟨C₀, c_A, hC₀_pos, hcA_ge1, fun {c'} hc' test => ?_⟩
  have hc'_pos : 0 < c' := by linarith
  have hε_pos : 0 < tipEps c' := tipEps_pos hc'_pos
  have hwt := hA hc' (test.toWeaklyFeasibleTest hc'_pos.le)
  rcases le_or_gt 0 (tipS₁ c' test) with hpos | hneg
  · linarith
  · have hlt : test.x₁ < xiStar := by
      have := hneg; unfold tipS₁ at this
      have : test.x₁ - xiStar < 0 := (div_neg_iff.mp this).elim
        (fun a => absurd a.2 (by linarith)) (fun b => b.1)
      linarith
    have hdiff_sq : (xiStar - test.x₁) * (xiStar + test.x₁) = xiStar ^ 2 - test.x₁ ^ 2 := by ring
    have hsq_bd : xiStar ^ 2 - test.x₁ ^ 2 ≤ 3 * C_A * tipEps c' := by
      have ht₁ : xiStar ^ 2 / 3 * c' - C_A * c' ^ (1 / 3 : ℝ) ≤ c' * test.x₁ ^ 2 / 3 := by
        dsimp [BlowupTest.toWeaklyFeasibleTest] at hwt
        rw [test.ht₁_eq, xiBar] at hwt
        linarith
      have hc13 : c' ^ (1 / 3 : ℝ) = c' * tipEps c' := by
        unfold tipEps
        calc c' ^ (1 / 3 : ℝ) = c' ^ (1 + -(2 / 3 : ℝ)) := by norm_num
          _ = c' ^ (1 : ℝ) * c' ^ (-(2 / 3 : ℝ)) := Real.rpow_add hc'_pos _ _
          _ = c' * c' ^ (-(2 / 3 : ℝ)) := by rw [Real.rpow_one]
      have hmul : c' * (xiStar ^ 2 - test.x₁ ^ 2) ≤ c' * (3 * C_A * tipEps c') := by
        rw [hc13] at ht₁; linarith
      exact le_of_mul_le_mul_left hmul hc'_pos
    have hsum_ge : xiStar ≤ xiStar + test.x₁ := by linarith [test.hx₁_nonneg]
    have hsub_nn : 0 ≤ xiStar - test.x₁ := by linarith
    have hlin : (xiStar - test.x₁) * xiStar ≤ 3 * C_A * tipEps c' :=
      (mul_le_mul_of_nonneg_left hsum_ge hsub_nn).trans (hdiff_sq ▸ hsq_bd)
    have hdiv : xiStar - test.x₁ ≤ C₀ * tipEps c' := by
      dsimp [C₀]
      calc xiStar - test.x₁ = ((xiStar - test.x₁) * xiStar) / xiStar := by
            field_simp [xiStar_pos.ne']
        _ ≤ (3 * C_A * tipEps c') / xiStar :=
            div_le_div_of_nonneg_right hlin xiStar_pos.le
        _ = (3 * C_A / xiStar) * tipEps c' := by ring
    unfold tipS₁
    rw [le_div_iff₀ hε_pos]
    linarith

/-- **Proposition T** (`blowup_limit.tex`, Proposition `bl:T`, parts (i)--(vi)):
Given any sequence `c_k → ∞` and concrete weakly feasible tests `test_k : BlowupTest inp (c_k)` whose
normalized tip thresholds `s₁(c_k)` are bounded above, `(s₁)` is bounded below by Theorem A and
there exists a subsequence `(ms k)` along which `s₁ → s₁*`, `γ → γLim`, and
`Φ_k = tipRescale (c_k) (test_k)` converges locally uniformly on `ℂ` to a real entire function `Ψ`
satisfying:
- **(i)** `‖Ψ ζ‖ ≤ C_env (1 + ‖ζ‖)^{1/2} airyEnv (-β ζ)`, off-axis sharp bound
  `‖Ψ ζ‖ ≤ C_env exp(H(ζ)) (1 + min((1 + ‖ζ‖)^{1/2}, 1/|Im ζ|))`, and sector gain
  `‖Ψ ζ‖ ≤ C_env exp(H(ζ)) / ‖ζ‖` on `|arg(-ζ)| ≤ 2π/3, ‖ζ‖ ≥ 8`;
- **(ii)** `Ψ ∈ L¹(ℝ)` and `∫_ℝ ‖Ψ‖ ≤ 1`;
- **(iii)** `(Ψ s).im = 0` on `ℝ` and `0 ≤ (Ψ s).re` on `[s₁*, ∞)`;
- **(iv)** `0 ≤ γLim`, `0 ≤ mEsc`, and `∫_ℝ (Ψ s).re = -(γLim + mEsc)`;
- **(v)** `1/2 ≤ ∫_ℝ max 0 (-(Ψ s).re)` and `Ψ ≢ 0`;
- **(vi)** `f(u) := Ψ (-u / β)` satisfies the `G_{1/2}` growth, `L¹`, sign, and non-positivity
  hypotheses, and `Ψ` has exponential order at most `3/2`. -/
theorem proposition_T (hI0 : BesselI0Asymptotic) (inp : StripBootstrapInputs)
    {c' : ℕ → ℝ} (hc' : Tendsto c' atTop atTop)
    (tests : ∀ k : ℕ, BlowupTest inp (c' k))
    (hB : ∃ B : ℝ, ∀ k : ℕ, tipS₁ (c' k) (tests k) ≤ B) :
    ∃ (ms : ℕ → ℕ) (s₁Star : ℝ) (Ψ : ℂ → ℂ) (γLim mEsc C_env : ℝ),
      StrictMono ms ∧
      Tendsto (fun k => tipS₁ (c' (ms k)) (tests (ms k))) atTop (nhds s₁Star) ∧
      TendstoLocallyUniformlyOn (fun k => tipRescale (c' (ms k)) (tests (ms k))) Ψ atTop univ ∧
      Tendsto (fun k => (tests (ms k)).gVac / (2 * π * (tests (ms k)).M)) atTop (nhds γLim) ∧
      -- (i) entire + growth bounds
      Differentiable ℂ Ψ ∧
      0 ≤ C_env ∧
      (∀ ζ : ℂ, ‖Ψ ζ‖ ≤ C_env * (1 + ‖ζ‖) ^ (1 / 2 : ℝ) * airyEnv (-(betaTip : ℂ) * ζ)) ∧
      (∀ ζ : ℂ, ζ.im ≠ 0 →
        ‖Ψ ζ‖ ≤ C_env * Real.exp (tipH ζ) *
          (1 + min ((1 + ‖ζ‖) ^ (1 / 2 : ℝ)) (1 / |ζ.im|))) ∧
      (∀ ζ : ℂ, |(-ζ).arg| ≤ 2 * π / 3 → 8 ≤ ‖ζ‖ →
        ‖Ψ ζ‖ ≤ C_env * Real.exp (tipH ζ) / ‖ζ‖) ∧
      -- (ii) L¹
      Integrable (fun s : ℝ => Ψ (s : ℂ)) ∧
      (∫ s : ℝ, ‖Ψ (s : ℂ)‖ ≤ 1) ∧
      -- (iii) real on ℝ, nonnegative on [s₁Star, ∞)
      (∀ s : ℝ, (Ψ (s : ℂ)).im = 0) ∧
      (∀ s : ℝ, s₁Star ≤ s → 0 ≤ (Ψ (s : ℂ)).re) ∧
      -- (iv) vacuum + escape mass
      0 ≤ γLim ∧ 0 ≤ mEsc ∧
      (∫ s : ℝ, (Ψ (s : ℂ)).re) = -(γLim + mEsc) ∧
      -- (v) half-mass + non-vanishing
      ((1 / 2 : ℝ) ≤ ∫ s : ℝ, max 0 (-(Ψ (s : ℂ)).re)) ∧
      (∃ z : ℂ, Ψ z ≠ 0) ∧
      -- (vi) `G_{1/2}` rescaling `f(u) = Ψ(-u/β)` and order `≤ 3/2`
      (let f : ℂ → ℂ := fun u => Ψ (-u / (betaTip : ℂ))
       Differentiable ℂ f ∧
       (∃ C_f : ℝ, 0 ≤ C_f ∧ ∀ u : ℂ, ‖f u‖ ≤ C_f * (1 + ‖u‖) ^ (1 / 2 : ℝ) * airyEnv u) ∧
       Integrable (fun u : ℝ => f (u : ℂ)) ∧
       (∃ u : ℂ, f u ≠ 0) ∧
       (∀ u : ℝ, (f (u : ℂ)).im = 0) ∧
       (∀ u : ℝ, u ≤ -betaTip * s₁Star → 0 ≤ (f (u : ℂ)).re) ∧
       (∫ u : ℝ, (f (u : ℂ)).re) ≤ 0 ∧
       (∀ ε : ℝ, 0 < ε → ∃ C_ord : ℝ, 0 ≤ C_ord ∧
         ∀ ζ : ℂ, ‖Ψ ζ‖ ≤ C_ord * Real.exp ((KTip + ε) * ‖ζ‖ ^ (3 / 2 : ℝ)))) := by
  obtain ⟨B, hB_le⟩ := hB
  obtain ⟨C₀, c_A, hC₀_pos, hcA_ge1, hA⟩ := tipS₁_theorem_A_lower inp
  obtain ⟨C_env, hCenv_nn, hEnv⟩ := tipRescale_pointwise_envelope hI0 inp
  obtain ⟨η, hη_tend, hTail⟩ := blowup_left_tail_bound inp
  -- Step 1: Pass to tail `k ≥ K₀` where `c' k ≥ max c_A 39`, extract `(ms₁)` so `s₁` & `γ` converge.
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.mp (hc'.eventually (eventually_ge_atTop (max c_A 39)))
  let s1_seq : ℕ → ℝ := fun k => tipS₁ (c' (k + K₀)) (tests (k + K₀))
  let γ_seq : ℕ → ℝ := fun k => (tests (k + K₀)).gVac / (2 * π * (tests (k + K₀)).M)
  have hs1_bdd : ∀ k : ℕ, s1_seq k ∈ Icc (-C₀) B := fun k => by
    have hc'k := hK₀ (k + K₀) (Nat.le_add_left K₀ k)
    exact ⟨hA ((le_max_left _ _).trans hc'k) _, hB_le _⟩
  have hγ_bdd : ∀ k : ℕ, γ_seq k ∈ Icc (0 : ℝ) 1 := fun k => by
    have hc'k : 0 < c' (k + K₀) := by
      have hc'_le : (39 : ℝ) ≤ c' (k + K₀) := (le_max_right _ _).trans (hK₀ (k + K₀) (Nat.le_add_left K₀ k))
      linarith
    let htest := tests (k + K₀)
    have hvac := tipRescale_integral_vac hc'k htest
    have hnorm := tipRescale_norm_integral hc'k htest
    have h_le : -(∫ s in Ioi (tipSMin (c' (k + K₀))), (tipRescale (c' (k + K₀)) htest (s : ℂ)).re) ≤
        ∫ s in Ioi (tipSMin (c' (k + K₀))), ‖tipRescale (c' (k + K₀)) htest (s : ℂ)‖ := by
      calc -(∫ s in Ioi (tipSMin (c' (k + K₀))), (tipRescale (c' (k + K₀)) htest (s : ℂ)).re)
          ≤ |∫ s in Ioi (tipSMin (c' (k + K₀))), (tipRescale (c' (k + K₀)) htest (s : ℂ)).re| :=
            neg_le_abs _
        _ = ‖∫ s in Ioi (tipSMin (c' (k + K₀))), (tipRescale (c' (k + K₀)) htest (s : ℂ)).re‖ :=
            (Real.norm_eq_abs _).symm
        _ ≤ ∫ s in Ioi (tipSMin (c' (k + K₀))), ‖(tipRescale (c' (k + K₀)) htest (s : ℂ)).re‖ :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ s in Ioi (tipSMin (c' (k + K₀))), ‖tipRescale (c' (k + K₀)) htest (s : ℂ)‖ := by
            refine setIntegral_mono_on
              (tipRescale_integrableOn_domain hc'k htest).re.norm
              (tipRescale_integrableOn_domain hc'k htest).norm measurableSet_Ioi fun s _ => ?_
            exact (Complex.abs_re_le_norm _).trans_eq rfl
    have hvac_nn : 0 ≤ γ_seq k := by
      dsimp [γ_seq, htest]
      exact div_nonneg (tests (k + K₀)).hgVac_nonneg (by positivity [Real.pi_pos, (tests (k + K₀)).hM_pos])
    refine ⟨hvac_nn, ?_⟩
    dsimp [γ_seq, htest] at h_le ⊢
    linarith [hvac, hnorm]
  obtain ⟨s₁Star, _, φ₁, hφ₁_strict, hs₁_lim⟩ :=
    isCompact_Icc.tendsto_subseq (x := s1_seq) hs1_bdd
  obtain ⟨γLim, _, φ₂, hφ₂_strict, hγ_lim⟩ :=
    isCompact_Icc.tendsto_subseq (x := fun m => γ_seq (φ₁ m)) (fun m => hγ_bdd _)
  -- Step 2: Montel exhaustion on `k ↦ tipRescale (c' (φ₁ (φ₂ k) + K₀))`.
  let idx₁ : ℕ → ℕ := fun m => φ₁ (φ₂ m) + K₀
  have hidx₁_strict : StrictMono idx₁ :=
    fun a b hab => Nat.add_lt_add_right (hφ₁_strict (hφ₂_strict hab)) K₀
  have hc'_idx₁ : Tendsto (fun m => c' (idx₁ m)) atTop atTop :=
    hc'.comp hidx₁_strict.tendsto_atTop
  let F : ℕ → ℂ → ℂ := fun m => tipRescale (c' (idx₁ m)) (tests (idx₁ m))
  have hF_hol : ∀ R : ℝ, 0 ≤ R → ∀ᶠ m in atTop, DifferentiableOn ℂ (F m) (ball 0 R) := by
    intro R hR
    have hεR : Tendsto (fun m => 2 * R * tipEps (c' (idx₁ m))) atTop (nhds 0) := by
      have h0 := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp hc'_idx₁
      simpa [tipEps] using h0.const_mul (2 * R)
    filter_upwards [hc'_idx₁.eventually (eventually_ge_atTop (1 : ℝ)),
      hεR.eventually (eventually_lt_nhds one_pos)] with m hc'1 h2R
    exact tipRescale_holo_ball (by linarith) h2R (tests (idx₁ m))
  have hF_bdd : ∀ R : ℝ, 0 ≤ R → ∃ M : ℝ, ∀ᶠ m in atTop, ∀ z ∈ ball 0 R, ‖F m z‖ ≤ M := by
    intro R hR
    let M : ℝ := C_env * (1 + R) ^ (1 / 2 : ℝ) * Real.exp (KTip * R ^ (3 / 2 : ℝ))
    refine ⟨M, ?_⟩
    filter_upwards [hc'_idx₁.eventually (hEnv R hR)] with m hm z hz
    have hz_cl : z ∈ closedBall (0 : ℂ) R := ball_subset_closedBall hz
    have h1 := (hm (tests (idx₁ m)) z hz_cl).1
    have hz_le : ‖z‖ ≤ R := by simpa [mem_closedBall, dist_zero_right] using hz_cl
    have hH_le : tipH z ≤ KTip * R ^ (3 / 2 : ℝ) := by
      unfold tipH
      have hre : -((-z) ^ (3 / 2 : ℂ)).re ≤ ‖z‖ ^ (3 / 2 : ℝ) := by
        simpa [norm_neg] using FormalResearch.Special.re_cpow_three_halves_le (-z)
      have hpow_le : ‖z‖ ^ (3 / 2 : ℝ) ≤ R ^ (3 / 2 : ℝ) := Real.rpow_le_rpow (norm_nonneg _) hz_le (by norm_num)
      calc -KTip * ((-z) ^ (3 / 2 : ℂ)).re = KTip * (-((-z) ^ (3 / 2 : ℂ)).re) := by ring
        _ ≤ KTip * ‖z‖ ^ (3 / 2 : ℝ) := mul_le_mul_of_nonneg_left hre KTip_pos.le
        _ ≤ KTip * R ^ (3 / 2 : ℝ) := mul_le_mul_of_nonneg_left hpow_le KTip_pos.le
    calc ‖F m z‖ ≤ C_env * (1 + ‖z‖) ^ (1 / 2 : ℝ) * Real.exp (tipH z) := h1
      _ ≤ C_env * (1 + R) ^ (1 / 2 : ℝ) * Real.exp (KTip * R ^ (3 / 2 : ℝ)) := by
          gcongr
  obtain ⟨φ₃, Ψ, hφ₃_strict, hΨ_diff, hΨ_lim⟩ := montel_exhaustion_entire F hF_hol hF_bdd
  let ms : ℕ → ℕ := fun k => idx₁ (φ₃ k)
  have hms_strict : StrictMono ms := hidx₁_strict.comp hφ₃_strict
  have hs₁_sub : Tendsto (fun k => tipS₁ (c' (ms k)) (tests (ms k))) atTop (nhds s₁Star) :=
    (hs₁_lim.comp hφ₂_strict.tendsto_atTop).comp hφ₃_strict.tendsto_atTop
  have hγ_sub : Tendsto (fun k => (tests (ms k)).gVac / (2 * π * (tests (ms k)).M))
      atTop (nhds γLim) :=
    hγ_lim.comp hφ₃_strict.tendsto_atTop
  have hc'_ms : Tendsto (fun k => c' (ms k)) atTop atTop := hc'.comp hms_strict.tendsto_atTop
  -- Step 3: Prove (i) pointwise sharp bounds for `Ψ`.
  have hΨ_pt : ∀ ζ : ℂ, tipH ζ ≤ KTip * ‖ζ‖ ^ (3 / 2 : ℝ) := fun ζ => by
    unfold tipH
    have hre : -((-ζ) ^ (3 / 2 : ℂ)).re ≤ ‖ζ‖ ^ (3 / 2 : ℝ) := by
      simpa [norm_neg] using FormalResearch.Special.re_cpow_three_halves_le (-ζ)
    calc -KTip * ((-ζ) ^ (3 / 2 : ℂ)).re = KTip * (-((-ζ) ^ (3 / 2 : ℂ)).re) := by ring
      _ ≤ KTip * ‖ζ‖ ^ (3 / 2 : ℝ) := mul_le_mul_of_nonneg_left hre KTip_pos.le
  have hΨ_i1 : ∀ ζ : ℂ, ‖Ψ ζ‖ ≤ C_env * (1 + ‖ζ‖) ^ (1 / 2 : ℝ) * airyEnv (-(betaTip : ℂ) * ζ) := by
    intro ζ
    rw [← tipH_eq_airyEnv ζ]
    have hlim : Tendsto (fun k => ‖F (φ₃ k) ζ‖) atTop (nhds ‖Ψ ζ‖) :=
      (continuous_norm.tendsto _).comp (hΨ_lim.tendsto_at (mem_univ ζ))
    have hcl : ζ ∈ closedBall (0 : ℂ) ‖ζ‖ := mem_closedBall_zero_iff.mpr le_rfl
    have hev : ∀ᶠ k in atTop, ‖F (φ₃ k) ζ‖ ≤
        C_env * (1 + ‖ζ‖) ^ (1 / 2 : ℝ) * Real.exp (tipH ζ) := by
      filter_upwards [(hc'_ms.eventually (hEnv ‖ζ‖ (norm_nonneg ζ)))] with k hk
      exact (hk (tests (ms k)) ζ hcl).1
    exact le_of_tendsto hlim hev
  have hΨ_i2 : ∀ ζ : ℂ, ζ.im ≠ 0 →
      ‖Ψ ζ‖ ≤ C_env * Real.exp (tipH ζ) * (1 + min ((1 + ‖ζ‖) ^ (1 / 2 : ℝ)) (1 / |ζ.im|)) := by
    intro ζ him
    have hlim : Tendsto (fun k => ‖F (φ₃ k) ζ‖) atTop (nhds ‖Ψ ζ‖) :=
      (continuous_norm.tendsto _).comp (hΨ_lim.tendsto_at (mem_univ ζ))
    have hcl : ζ ∈ closedBall (0 : ℂ) ‖ζ‖ := mem_closedBall_zero_iff.mpr le_rfl
    have hev : ∀ᶠ k in atTop, ‖F (φ₃ k) ζ‖ ≤
        C_env * Real.exp (tipH ζ) * (1 + min ((1 + ‖ζ‖) ^ (1 / 2 : ℝ)) (1 / |ζ.im|)) := by
      filter_upwards [(hc'_ms.eventually (hEnv ‖ζ‖ (norm_nonneg ζ)))] with k hk
      exact (hk (tests (ms k)) ζ hcl).2.1 him
    exact le_of_tendsto hlim hev
  have hΨ_i3 : ∀ ζ : ℂ, |(-ζ).arg| ≤ 2 * π / 3 → 8 ≤ ‖ζ‖ →
      ‖Ψ ζ‖ ≤ C_env * Real.exp (tipH ζ) / ‖ζ‖ := by
    intro ζ harg h8
    have hlim : Tendsto (fun k => ‖F (φ₃ k) ζ‖) atTop (nhds ‖Ψ ζ‖) :=
      (continuous_norm.tendsto _).comp (hΨ_lim.tendsto_at (mem_univ ζ))
    have hcl : ζ ∈ closedBall (0 : ℂ) ‖ζ‖ := mem_closedBall_zero_iff.mpr le_rfl
    have hev : ∀ᶠ k in atTop, ‖F (φ₃ k) ζ‖ ≤ C_env * Real.exp (tipH ζ) / ‖ζ‖ := by
      filter_upwards [(hc'_ms.eventually (hEnv ‖ζ‖ (norm_nonneg ζ)))] with k hk
      exact (hk (tests (ms k)) ζ hcl).2.2 harg h8
    exact le_of_tendsto hlim hev
  -- Step 4: (iii) real on `ℝ`, nonnegative on `[s₁Star, ∞)`.
  have hΨ_im : ∀ s : ℝ, (Ψ (s : ℂ)).im = 0 := fun s => by
    have hlim : Tendsto (fun k => (F (φ₃ k) (s : ℂ)).im) atTop (nhds (Ψ (s : ℂ)).im) :=
      (Complex.continuous_im.tendsto _).comp (hΨ_lim.tendsto_at (mem_univ (s : ℂ)))
    have heq0 : (fun k => (F (φ₃ k) (s : ℂ)).im) = fun _ => 0 := funext fun k =>
      tipRescale_im_eq_zero (tests (ms k)) s
    rw [heq0] at hlim
    exact tendsto_nhds_unique hlim tendsto_const_nhds
  have hΨ_nonneg_open : ∀ s : ℝ, s₁Star < s → 0 ≤ (Ψ (s : ℂ)).re := fun s hs => by
    have hlim : Tendsto (fun k => (F (φ₃ k) (s : ℂ)).re) atTop (nhds (Ψ (s : ℂ)).re) :=
      (Complex.continuous_re.tendsto _).comp (hΨ_lim.tendsto_at (mem_univ (s : ℂ)))
    have hev : ∀ᶠ k in atTop, 0 ≤ (F (φ₃ k) (s : ℂ)).re := by
      filter_upwards [hs₁_sub.eventually (eventually_le_nhds hs),
        hc'_ms.eventually (eventually_gt_atTop (0 : ℝ))] with k hsk hc'k
      exact tipRescale_nonneg_tail hc'k (tests (ms k)) s hsk
    exact ge_of_tendsto hlim hev
  have hΨ_nonneg : ∀ s : ℝ, s₁Star ≤ s → 0 ≤ (Ψ (s : ℂ)).re := fun s hs => by
    rcases eq_or_lt_of_le hs with rfl | hlt
    · have hseq : Tendsto (fun n : ℕ => s₁Star + ((n : ℝ) + 1)⁻¹) atTop (nhds s₁Star) := by
        simpa [one_div] using
          (tendsto_const_nhds (x := s₁Star)).add tendsto_one_div_add_atTop_nhds_zero_nat
      have hcont : ContinuousAt (fun t : ℝ => (Ψ (t : ℂ)).re) s₁Star :=
        (Complex.continuous_re.comp (hΨ_diff.continuous.comp Complex.continuous_ofReal)).continuousAt
      exact ge_of_tendsto (hcont.tendsto.comp hseq) (Eventually.of_forall fun n =>
        hΨ_nonneg_open _ (by linarith [show (0 : ℝ) < ((n : ℝ) + 1)⁻¹ by positivity]))
    · exact hΨ_nonneg_open s hlt
  -- Step 5: (ii) `∫_{-R}^R ‖Ψ‖ ≤ 1` -> `Ψ ∈ L¹(ℝ)` and `∫_ℝ ‖Ψ‖ ≤ 1`.
  have hΨ_Ioc_le : ∀ R : ℝ, 0 ≤ R → ∫ s in Ioc (-R) R, ‖Ψ (s : ℂ)‖ ≤ 1 := fun R hR => by
    have hunif : TendstoUniformlyOn (fun k (s : ℝ) => ‖F (φ₃ k) (s : ℂ)‖) (fun (s : ℝ) => ‖Ψ (s : ℂ)‖) atTop
        (Icc (-R) R : Set ℝ) := by
      have hK : IsCompact (Complex.ofReal '' Icc (-R) R) := isCompact_Icc.image Complex.continuous_ofReal
      have hu := ((tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ).mp hΨ_lim)
        _ (subset_univ _) hK
      rw [Metric.tendstoUniformlyOn_iff] at hu ⊢
      intro ε hε
      filter_upwards [hu ε hε] with k hk s hs
      have hd := hk (s : ℂ) (mem_image_of_mem _ hs)
      rw [Real.dist_eq]
      rw [Complex.dist_eq] at hd
      exact (abs_norm_sub_norm_le (Ψ (s : ℂ)) (F (φ₃ k) (s : ℂ))).trans_lt hd
    have hcont_Ψ : ContinuousOn (fun s : ℝ => ‖Ψ (s : ℂ)‖) (Icc (-R) R) :=
      (continuous_norm.comp (hΨ_diff.continuous.comp Complex.continuous_ofReal)).continuousOn
    have hint_ev : ∀ᶠ k in atTop,
        IntervalIntegrable (fun s : ℝ => ‖F (φ₃ k) (s : ℂ)‖) volume (-R) R := by
      filter_upwards [hc'_ms.eventually (eventually_gt_atTop (0 : ℝ))] with k hc'k
      have hcont : ContinuousOn (fun s : ℝ => ‖F (φ₃ k) (s : ℂ)‖) (Icc (-R) R) := by
        have hb : ContinuousOn (fun s : ℝ => F (φ₃ k) (s : ℂ)) (Icc (-R) R) :=
          (tipRescale_holo hc'k (tests (ms k))).continuousOn.comp
            Complex.continuous_ofReal.continuousOn fun s _ => by
              rw [mem_ofPred_eq, Complex.ofReal_im, abs_zero]
              exact one_div_pos.mpr (by positivity [tipEps_pos hc'k])
        exact hb.norm
      exact hcont.intervalIntegrable_of_Icc (by linarith)
    have hlim_int : Tendsto (fun k => ∫ s in (-R)..R, ‖F (φ₃ k) (s : ℂ)‖) atTop
        (nhds (∫ s in (-R)..R, ‖Ψ (s : ℂ)‖)) :=
      intervalIntegral_tendsto_of_tendstoUniformlyOn (by linarith) hunif hint_ev hcont_Ψ
    have hev_le1 : ∀ᶠ k in atTop, ∫ s in (-R)..R, ‖F (φ₃ k) (s : ℂ)‖ ≤ 1 := by
      have hsMin_tend : Tendsto (fun k => tipSMin (c' (ms k))) atTop atBot := by
        unfold tipSMin
        simpa [neg_mul] using tendsto_neg_atBot_iff.mpr
          (((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp hc'_ms).const_mul_atTop
            xiStar_pos)
      filter_upwards [hsMin_tend.eventually (eventually_lt_atBot (-R)),
        hc'_ms.eventually (eventually_gt_atTop (0 : ℝ))] with k hsMin hc'k
      rw [intervalIntegral.integral_of_le (by linarith)]
      have hnorm_eq := tipRescale_norm_integral hc'k (tests (ms k))
      have hint_dom := (tipRescale_integrableOn_domain hc'k (tests (ms k))).norm
      have hsub : Ioc (-R) R ⊆ Ioi (tipSMin (c' (ms k))) := fun s hs => lt_trans hsMin hs.1
      calc ∫ s in Ioc (-R) R, ‖F (φ₃ k) (s : ℂ)‖
          ≤ ∫ s in Ioi (tipSMin (c' (ms k))), ‖F (φ₃ k) (s : ℂ)‖ :=
            setIntegral_mono_set hint_dom (ae_of_all _ fun _ => norm_nonneg _) hsub.eventuallySubset
        _ = 1 := hnorm_eq
    rw [← intervalIntegral.integral_of_le (by linarith)]
    exact le_of_tendsto hlim_int hev_le1
  have hΨ_int : Integrable (fun s : ℝ => Ψ (s : ℂ)) := by
    have hcont : Continuous (fun s : ℝ => Ψ (s : ℂ)) :=
      hΨ_diff.continuous.comp Complex.continuous_ofReal
    have hlint : ∫⁻ s : ℝ, ‖Ψ (s : ℂ)‖ₑ ≤ 1 := by
      let g : ℕ → ℝ → ENNReal := fun n => (Ioc (-(n : ℝ)) n).indicator (fun s => ‖Ψ (s : ℂ)‖ₑ)
      have hmono : Monotone g := fun m n hmn s => by
        dsimp [g]
        by_cases hm : s ∈ Ioc (-(m : ℝ)) m
        · have hn : s ∈ Ioc (-(n : ℝ)) n :=
            ⟨by linarith [hm.1, show (m : ℝ) ≤ n by exact_mod_cast hmn],
             by linarith [hm.2, show (m : ℝ) ≤ n by exact_mod_cast hmn]⟩
          rw [indicator_of_mem hm, indicator_of_mem hn]
        · rw [indicator_of_notMem hm]; exact bot_le
      have hlim : ∀ s : ℝ, Tendsto (fun n : ℕ => g n s) atTop (nhds ‖Ψ (s : ℂ)‖ₑ) := fun s => by
        obtain ⟨n₀, hn₀⟩ := exists_nat_gt |s|
        have hev : ∀ᶠ n in atTop, g n s = ‖Ψ (s : ℂ)‖ₑ := by
          filter_upwards [eventually_ge_atTop n₀] with n hn
          have hmem : s ∈ Ioc (-(n : ℝ)) n := by
            have hle : |s| < n := lt_of_lt_of_le hn₀ (by exact_mod_cast hn)
            rw [abs_lt] at hle
            exact ⟨hle.1, hle.2.le⟩
          exact indicator_of_mem hmem _
        exact tendsto_const_nhds.congr' (hev.mono fun _ h => h.symm)
      have hmeas : ∀ n : ℕ, Measurable (g n) := fun n =>
        hcont.enorm.measurable.indicator measurableSet_Ioc
      have hl := lintegral_tendsto_of_tendsto_of_monotone (μ := volume)
        (fun n => (hmeas n).aemeasurable)
        (ae_of_all volume fun s _ _ hmn => hmono hmn s) (ae_of_all volume hlim)
      have hle1 : ∀ n : ℕ, ∫⁻ s : ℝ, g n s ≤ 1 := fun n => by
        rw [lintegral_indicator measurableSet_Ioc]
        have hIoc_int : IntegrableOn (fun s : ℝ => ‖Ψ (s : ℂ)‖) (Ioc (-(n : ℝ)) n) :=
          (hcont.norm.continuousOn (s := Icc (-(n : ℝ)) n)).integrableOn_Icc.mono_set
            Ioc_subset_Icc_self
        have h_eq : ∫⁻ s in Ioc (-(n : ℝ)) n, ‖Ψ (s : ℂ)‖ₑ =
            ENNReal.ofReal (∫ s in Ioc (-(n : ℝ)) n, ‖Ψ (s : ℂ)‖) := by
          rw [ofReal_integral_eq_lintegral_ofReal hIoc_int (Eventually.of_forall fun _ => norm_nonneg _)]
          congr 1; ext s; exact (ofReal_norm _).symm
        rw [h_eq]
        exact ENNReal.ofReal_le_one.mpr (hΨ_Ioc_le n (Nat.cast_nonneg n))
      exact le_of_tendsto hl (Eventually.of_forall hle1)
    exact ⟨hcont.aestronglyMeasurable, lt_of_le_of_lt hlint ENNReal.one_lt_top⟩
  have hΨ_norm_le : ∫ s : ℝ, ‖Ψ (s : ℂ)‖ ≤ 1 := by
    have htend_int : Tendsto (fun n : ℕ => ∫ s in Ioc (-(n : ℝ)) n, ‖Ψ (s : ℂ)‖) atTop
        (nhds (∫ s : ℝ, ‖Ψ (s : ℂ)‖)) := by
      have heq : ∀ n : ℕ, ∫ s in Ioc (-(n : ℝ)) n, ‖Ψ (s : ℂ)‖ =
          ∫ s : ℝ, (Ioc (-(n : ℝ)) n).indicator (fun t => ‖Ψ (t : ℂ)‖) s :=
        fun n => (integral_indicator measurableSet_Ioc).symm
      simp_rw [heq]
      refine tendsto_integral_of_dominated_convergence (fun s => ‖Ψ (s : ℂ)‖)
        (fun n => (hΨ_int.norm.indicator measurableSet_Ioc).aestronglyMeasurable)
        hΨ_int.norm
        (fun n => Eventually.of_forall fun s => by
          rw [Real.norm_of_nonneg (indicator_nonneg (fun _ _ => norm_nonneg _) _)]
          simp only [Set.indicator]; split_ifs <;> [exact le_rfl; exact norm_nonneg _])
        (Eventually.of_forall fun s => by
          obtain ⟨n₀, hn₀⟩ := exists_nat_gt |s|
          refine tendsto_const_nhds.congr' (eventually_ge_atTop n₀ |>.mono fun n hn => ?_)
          have hle : |s| < n := lt_of_lt_of_le hn₀ (by exact_mod_cast hn)
          rw [abs_lt] at hle
          have hmem : s ∈ Ioc (-(n : ℝ)) n := ⟨hle.1, hle.2.le⟩
          simp [Set.indicator, hmem])
    exact le_of_tendsto htend_int (Eventually.of_forall fun n => hΨ_Ioc_le n (Nat.cast_nonneg n))
  -- Step 6: (iv) `γLim ≥ 0`, `mEsc ≥ 0`, `∫ (Ψ s).re = -(γLim + mEsc)`.
  have hγLim_nn : 0 ≤ γLim := by
    refine ge_of_tendsto hγ_sub (Eventually.of_forall fun k => ?_)
    exact div_nonneg (tests (ms k)).hgVac_nonneg (by positivity [Real.pi_pos, (tests (ms k)).hM_pos])
  have hΨ_re_le_neg_γ : ∫ s : ℝ, (Ψ (s : ℂ)).re ≤ -γLim := by
    have hR_bound : ∀ R : ℝ, max 1 (|s₁Star| + 1) ≤ R →
        ∫ s in Ioc (-R) R, (Ψ (s : ℂ)).re ≤ -γLim + η R := by
      intro R hR
      have hR1 : 1 ≤ R := (le_max_left _ _).trans hR
      have hRs1 : s₁Star + 1 ≤ R := by linarith [(le_max_right 1 (|s₁Star| + 1)).trans hR, le_abs_self s₁Star]
      have hunif : TendstoUniformlyOn (fun k (s : ℝ) => (F (φ₃ k) (s : ℂ)).re) (fun (s : ℝ) => (Ψ (s : ℂ)).re)
          atTop (Icc (-R) R : Set ℝ) := by
        have hK : IsCompact (Complex.ofReal '' Icc (-R) R) := isCompact_Icc.image Complex.continuous_ofReal
        have hu := ((tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ).mp hΨ_lim)
          _ (subset_univ _) hK
        rw [Metric.tendstoUniformlyOn_iff] at hu ⊢
        intro ε hε
        filter_upwards [hu ε hε] with k hk s hs
        have hd := hk (s : ℂ) (mem_image_of_mem _ hs)
        rw [Real.dist_eq]
        rw [Complex.dist_eq] at hd
        calc |(Ψ (s : ℂ)).re - (F (φ₃ k) (s : ℂ)).re|
            = |(Ψ (s : ℂ) - F (φ₃ k) (s : ℂ)).re| := by simp [Complex.sub_re]
          _ ≤ ‖Ψ (s : ℂ) - F (φ₃ k) (s : ℂ)‖ := Complex.abs_re_le_norm _
          _ < ε := hd
      have hcont_Ψ : ContinuousOn (fun s : ℝ => (Ψ (s : ℂ)).re) (Icc (-R) R) :=
        (Complex.continuous_re.comp (hΨ_diff.continuous.comp Complex.continuous_ofReal)).continuousOn
      have hint_ev : ∀ᶠ k in atTop,
          IntervalIntegrable (fun s : ℝ => (F (φ₃ k) (s : ℂ)).re) volume (-R) R := by
        filter_upwards [hc'_ms.eventually (eventually_gt_atTop (0 : ℝ))] with k hc'k
        have hcont : ContinuousOn (fun s : ℝ => (F (φ₃ k) (s : ℂ)).re) (Icc (-R) R) :=
          Complex.continuous_re.comp_continuousOn ((tipRescale_holo hc'k (tests (ms k))).continuousOn.comp
            Complex.continuous_ofReal.continuousOn (fun s _ => by
              rw [mem_ofPred_eq, Complex.ofReal_im, abs_zero]
              exact one_div_pos.mpr (by positivity [tipEps_pos hc'k])))
        exact hcont.intervalIntegrable_of_Icc (by linarith)
      have hlim_int : Tendsto (fun k => ∫ s in (-R)..R, (F (φ₃ k) (s : ℂ)).re) atTop
          (nhds (∫ s in (-R)..R, (Ψ (s : ℂ)).re)) :=
        intervalIntegral_tendsto_of_tendstoUniformlyOn (by linarith) hunif hint_ev hcont_Ψ
      have hsMin_tend : Tendsto (fun k => tipSMin (c' (ms k))) atTop atBot := by
        unfold tipSMin
        simpa [neg_mul] using tendsto_neg_atBot_iff.mpr
          (((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp hc'_ms).const_mul_atTop
            xiStar_pos)
      have hev_le : ∀ᶠ k in atTop,
          ∫ s in (-R)..R, (F (φ₃ k) (s : ℂ)).re ≤
            -((tests (ms k)).gVac / (2 * π * (tests (ms k)).M)) + η R := by
        filter_upwards [hsMin_tend.eventually (eventually_lt_atBot (-R)),
          hc'_ms.eventually (eventually_gt_atTop (0 : ℝ)),
          hc'_ms.eventually (hTail R hR1),
          hs₁_sub.eventually (eventually_le_nhds (by linarith : s₁Star < R))] with
          k hsMin hc'k htail_k hs₁_k
        have hdom := (tipRescale_integrableOn_domain hc'k (tests (ms k))).re
        have hsplit1 : (∫ s in Ioi (tipSMin (c' (ms k))), (F (φ₃ k) (s : ℂ)).re) =
            (∫ s in Ioc (tipSMin (c' (ms k))) R, (F (φ₃ k) (s : ℂ)).re) +
              ∫ s in Ioi R, (F (φ₃ k) (s : ℂ)).re := by
          have hltR : tipSMin (c' (ms k)) ≤ R := by linarith
          dsimp [F]
          rw [← Ioc_union_Ioi_eq_Ioi hltR]
          exact setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
            (hdom.mono_set Ioc_subset_Ioi_self) (hdom.mono_set (Ioi_subset_Ioi hltR))
        have hsplit2 : (∫ s in Ioc (tipSMin (c' (ms k))) R, (F (φ₃ k) (s : ℂ)).re) =
            (∫ s in Ioc (tipSMin (c' (ms k))) (-R), (F (φ₃ k) (s : ℂ)).re) +
              ∫ s in Ioc (-R) R, (F (φ₃ k) (s : ℂ)).re := by
          dsimp [F]
          rw [← Ioc_union_Ioc_eq_Ioc hsMin.le (by linarith)]
          exact setIntegral_union (Ioc_disjoint_Ioc_of_le (le_rfl : (-R : ℝ) ≤ -R)) measurableSet_Ioc
            (hdom.mono_set Ioc_subset_Ioi_self)
            (hdom.mono_set fun s hs => lt_trans hsMin hs.1)
        have hright_nn : 0 ≤ ∫ s in Ioi R, (F (φ₃ k) (s : ℂ)).re := by
          refine setIntegral_nonneg measurableSet_Ioi fun s hs => ?_
          exact tipRescale_nonneg_tail hc'k (tests (ms k)) s (hs₁_k.trans (mem_Ioi.mp hs).le)
        have hleft_bd : -η R ≤ ∫ s in Ioc (tipSMin (c' (ms k))) (-R), (F (φ₃ k) (s : ℂ)).re := by
          have h1 : |∫ s in Ioc (tipSMin (c' (ms k))) (-R), (F (φ₃ k) (s : ℂ)).re| ≤ η R := by
            calc |∫ s in Ioc (tipSMin (c' (ms k))) (-R), (F (φ₃ k) (s : ℂ)).re|
                = ‖∫ s in Ioc (tipSMin (c' (ms k))) (-R), (F (φ₃ k) (s : ℂ)).re‖ :=
                  (Real.norm_eq_abs _).symm
              _ ≤ ∫ s in Ioc (tipSMin (c' (ms k))) (-R), ‖(F (φ₃ k) (s : ℂ)).re‖ :=
                  norm_integral_le_integral_norm _
              _ ≤ ∫ s in Ioc (tipSMin (c' (ms k))) (-R), ‖F (φ₃ k) (s : ℂ)‖ := by
                  refine setIntegral_mono_on
                    (IntegrableOn.mono_set (hdom.mono_set Ioc_subset_Ioi_self).norm le_rfl)
                    (IntegrableOn.mono_set
                      (tipRescale_integrableOn_domain hc'k (tests (ms k))).norm Ioc_subset_Ioi_self)
                    measurableSet_Ioc fun s _ => (Complex.abs_re_le_norm _).trans_eq rfl
              _ ≤ η R := htail_k (tests (ms k))
          exact (abs_le.mp h1).1
        rw [intervalIntegral.integral_of_le (by linarith)]
        linarith [tipRescale_integral_vac hc'k (tests (ms k))]
      rw [← intervalIntegral.integral_of_le (by linarith)]
      exact le_of_tendsto_of_tendsto hlim_int (hγ_sub.neg.add_const (η R)) hev_le
    have htend_re : Tendsto (fun R : ℝ => ∫ s in Ioc (-R) R, (Ψ (s : ℂ)).re) atTop
        (nhds (∫ s : ℝ, (Ψ (s : ℂ)).re)) := by
      have heq : ∀ R : ℝ, ∫ s in Ioc (-R) R, (Ψ (s : ℂ)).re =
          ∫ s : ℝ, (Ioc (-R) R).indicator (fun t => (Ψ (t : ℂ)).re) s :=
        fun R => (integral_indicator measurableSet_Ioc).symm
      simp_rw [heq]
      refine tendsto_integral_filter_of_dominated_convergence (fun s => ‖(Ψ (s : ℂ)).re‖)
        (Eventually.of_forall fun R =>
          (hΨ_int.re.indicator measurableSet_Ioc).aestronglyMeasurable)
        (Eventually.of_forall fun R => Eventually.of_forall fun s => by
          by_cases hs : s ∈ Ioc (-R) R
          · rw [indicator_of_mem hs]
          · rw [indicator_of_notMem hs, norm_zero]; exact norm_nonneg _)
        hΨ_int.re.norm
        (Eventually.of_forall fun s => by
          refine tendsto_const_nhds.congr' (eventually_ge_atTop (|s| + 1) |>.mono fun R hR => ?_)
          have hle : |s| < R := by linarith
          rw [abs_lt] at hle
          have hmem : s ∈ Ioc (-R) R := ⟨hle.1, hle.2.le⟩
          simp [Set.indicator, hmem])
    have htend_rhs : Tendsto (fun R : ℝ => -γLim + η R) atTop (nhds (-γLim)) := by
      simpa using (tendsto_const_nhds (x := -γLim)).add hη_tend
    exact le_of_tendsto_of_tendsto htend_re htend_rhs
      (eventually_ge_atTop (max 1 (|s₁Star| + 1)) |>.mono fun R hR => hR_bound R hR)
  let mEsc : ℝ := -γLim - ∫ s : ℝ, (Ψ (s : ℂ)).re
  have hmEsc_nn : 0 ≤ mEsc := by dsimp [mEsc]; linarith
  have hre_eq : ∫ s : ℝ, (Ψ (s : ℂ)).re = -(γLim + mEsc) := by dsimp [mEsc]; ring
  -- Step 7: (v) `(1 / 2 : ℝ) ≤ ∫ s : ℝ, max 0 (-(Ψ (s : ℂ)).re)` and `Ψ ≢ 0`.
  have hneg_int : Integrable (fun s : ℝ => max 0 (-(Ψ (s : ℂ)).re)) := by
    have hcont : Continuous (fun s : ℝ => max 0 (-(Ψ (s : ℂ)).re)) :=
      continuous_const.max (Complex.continuous_re.comp
        (hΨ_diff.continuous.comp Complex.continuous_ofReal)).neg
    refine hΨ_int.norm.mono hcont.aestronglyMeasurable (Eventually.of_forall fun s => ?_)
    have hnn : 0 ≤ max 0 (-(Ψ (s : ℂ)).re) := le_max_left _ _
    rw [Real.norm_of_nonneg hnn, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact max_le (norm_nonneg _) ((neg_le_abs _).trans (Complex.abs_re_le_norm _))
  have hneg_half : (1 / 2 : ℝ) ≤ ∫ s : ℝ, max 0 (-(Ψ (s : ℂ)).re) := by
    obtain ⟨B_s1, hB_s1⟩ := eventually_atTop.mp
      (hs₁_sub.eventually (eventually_le_nhds (by linarith : s₁Star < s₁Star + 1)))
    have hR_bd : ∀ R : ℝ, max 1 (|s₁Star + 1| + 1) ≤ R →
        (1 / 2 : ℝ) - η R ≤ ∫ s : ℝ, max 0 (-(Ψ (s : ℂ)).re) := by
      intro R hR
      have hR1 : 1 ≤ R := (le_max_left _ _).trans hR
      have hRs1 : s₁Star + 1 ≤ R := by linarith [(le_max_right 1 (|s₁Star + 1| + 1)).trans hR, le_abs_self (s₁Star + 1)]
      have hunif : TendstoUniformlyOn (fun k (s : ℝ) => max 0 (-(F (φ₃ k) (s : ℂ)).re))
          (fun (s : ℝ) => max 0 (-(Ψ (s : ℂ)).re)) atTop (Icc (-R) R : Set ℝ) := by
        have hK : IsCompact (Complex.ofReal '' Icc (-R) R) := isCompact_Icc.image Complex.continuous_ofReal
        have hu := ((tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ).mp hΨ_lim)
          _ (subset_univ _) hK
        rw [Metric.tendstoUniformlyOn_iff] at hu ⊢
        intro ε hε
        filter_upwards [hu ε hε] with k hk s hs
        have hd := hk (s : ℂ) (mem_image_of_mem _ hs)
        rw [Real.dist_eq]
        rw [Complex.dist_eq] at hd
        have h1 : |max 0 (-(Ψ (s : ℂ)).re) - max 0 (-(F (φ₃ k) (s : ℂ)).re)| ≤
            |(Ψ (s : ℂ) - F (φ₃ k) (s : ℂ)).re| := by
          have hdist := (LipschitzWith.id.const_max (0 : ℝ)).dist_le_mul
            (-(Ψ (s : ℂ)).re) (-(F (φ₃ k) (s : ℂ)).re)
          rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul, id, id,
            show -(Ψ (s : ℂ)).re - -(F (φ₃ k) (s : ℂ)).re =
              -(Ψ (s : ℂ) - F (φ₃ k) (s : ℂ)).re by simp [Complex.sub_re]; ring,
            abs_neg] at hdist
          exact hdist
        exact lt_of_le_of_lt (h1.trans (Complex.abs_re_le_norm _)) hd
      have hcont_Ψ : ContinuousOn (fun s : ℝ => max 0 (-(Ψ (s : ℂ)).re)) (Icc (-R) R) :=
        (continuous_const.max (Complex.continuous_re.comp
          (hΨ_diff.continuous.comp Complex.continuous_ofReal)).neg).continuousOn
      have hint_ev : ∀ᶠ k in atTop,
          IntervalIntegrable (fun s : ℝ => max 0 (-(F (φ₃ k) (s : ℂ)).re)) volume (-R) R := by
        filter_upwards [hc'_ms.eventually (eventually_gt_atTop (0 : ℝ))] with k hc'k
        have hcont : ContinuousOn (fun s : ℝ => max 0 (-(F (φ₃ k) (s : ℂ)).re)) (Icc (-R) R) :=
          (continuous_const.max (continuous_id : Continuous fun x : ℝ => x)).comp_continuousOn
            ((Complex.continuous_re.comp_continuousOn
              ((tipRescale_holo hc'k (tests (ms k))).continuousOn.comp
                Complex.continuous_ofReal.continuousOn (fun s _ => by
                  rw [mem_ofPred_eq, Complex.ofReal_im, abs_zero]
                  exact one_div_pos.mpr (by positivity [tipEps_pos hc'k])))).neg)
        exact hcont.intervalIntegrable_of_Icc (by linarith)
      have hlim_int : Tendsto (fun k => ∫ s in (-R)..R, max 0 (-(F (φ₃ k) (s : ℂ)).re)) atTop
          (nhds (∫ s in (-R)..R, max 0 (-(Ψ (s : ℂ)).re))) :=
        intervalIntegral_tendsto_of_tendstoUniformlyOn (by linarith) hunif hint_ev hcont_Ψ
      have hsMin_tend : Tendsto (fun k => tipSMin (c' (ms k))) atTop atBot := by
        unfold tipSMin
        simpa [neg_mul] using tendsto_neg_atBot_iff.mpr
          (((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp hc'_ms).const_mul_atTop
            xiStar_pos)
      have hev_ge : ∀ᶠ k in atTop,
          (1 / 2 : ℝ) - η R ≤ ∫ s in (-R)..R, max 0 (-(F (φ₃ k) (s : ℂ)).re) := by
        filter_upwards [eventually_ge_atTop B_s1,
          hsMin_tend.eventually (eventually_lt_atBot (-R)),
          hc'_ms.eventually (eventually_gt_atTop (0 : ℝ)),
          hc'_ms.eventually (hTail R hR1)] with k hkB hsMin hc'k htail_k
        have hs1_le_R : tipS₁ (c' (ms k)) (tests (ms k)) ≤ R := (hB_s1 k hkB).trans hRs1
        have hhalf := tipRescale_half_neg_mass hc'k (tests (ms k))
        have hdom_norm := (tipRescale_integrableOn_domain hc'k (tests (ms k))).norm
        have hfneg_dom : IntegrableOn (fun s : ℝ => max 0 (-(F (φ₃ k) (s : ℂ)).re))
            (Ioi (tipSMin (c' (ms k)))) := by
          refine hdom_norm.mono ((continuous_const.max (continuous_id : Continuous fun x : ℝ => x)).comp_aestronglyMeasurable
            (tipRescale_integrableOn_domain hc'k (tests (ms k))).re.neg.aestronglyMeasurable)
            (Eventually.of_forall fun s => ?_)
          rw [Real.norm_of_nonneg (le_max_left _ _), Real.norm_of_nonneg (norm_nonneg _)]
          exact max_le (norm_nonneg _) ((neg_le_abs _).trans (Complex.abs_re_le_norm _))
        have hsub_tot : Ioc (tipSMin (c' (ms k))) (tipS₁ (c' (ms k)) (tests (ms k))) ⊆
            Ioc (tipSMin (c' (ms k))) R :=
          Ioc_subset_Ioc_right hs1_le_R
        have h1 : (1 / 2 : ℝ) ≤ ∫ s in Ioc (tipSMin (c' (ms k))) R,
            max 0 (-(F (φ₃ k) (s : ℂ)).re) :=
          hhalf.trans (setIntegral_mono_set (hfneg_dom.mono_set Ioc_subset_Ioi_self)
            (ae_of_all _ fun _ => le_max_left _ _) hsub_tot.eventuallySubset)
        have hsplit : (∫ s in Ioc (tipSMin (c' (ms k))) R, max 0 (-(F (φ₃ k) (s : ℂ)).re)) =
            (∫ s in Ioc (tipSMin (c' (ms k))) (-R), max 0 (-(F (φ₃ k) (s : ℂ)).re)) +
              ∫ s in Ioc (-R) R, max 0 (-(F (φ₃ k) (s : ℂ)).re) := by
          rw [← Ioc_union_Ioc_eq_Ioc hsMin.le (by linarith)]
          exact setIntegral_union (Ioc_disjoint_Ioc_of_le (le_rfl : (-R : ℝ) ≤ -R)) measurableSet_Ioc
            (hfneg_dom.mono_set Ioc_subset_Ioi_self)
            (hfneg_dom.mono_set fun s hs => lt_trans hsMin hs.1)
        have htail_neg : ∫ s in Ioc (tipSMin (c' (ms k))) (-R), max 0 (-(F (φ₃ k) (s : ℂ)).re) ≤
            η R := by
          calc ∫ s in Ioc (tipSMin (c' (ms k))) (-R), max 0 (-(F (φ₃ k) (s : ℂ)).re)
              ≤ ∫ s in Ioc (tipSMin (c' (ms k))) (-R), ‖F (φ₃ k) (s : ℂ)‖ := by
                refine setIntegral_mono_on
                  (hfneg_dom.mono_set Ioc_subset_Ioi_self)
                  (IntegrableOn.mono_set hdom_norm Ioc_subset_Ioi_self)
                  measurableSet_Ioc fun s _ =>
                  max_le (norm_nonneg _) ((neg_le_abs _).trans (Complex.abs_re_le_norm _))
            _ ≤ η R := htail_k (tests (ms k))
        rw [intervalIntegral.integral_of_le (by linarith)]
        linarith
      have hlim_le : ∫ s in (-R)..R, max 0 (-(Ψ (s : ℂ)).re) ≤
          ∫ s : ℝ, max 0 (-(Ψ (s : ℂ)).re) := by
        rw [intervalIntegral.integral_of_le (by linarith)]
        exact setIntegral_le_integral hneg_int (ae_of_all _ fun _ => le_max_left _ _)
      linarith [ge_of_tendsto hlim_int hev_ge]
    have htend_lhs : Tendsto (fun R : ℝ => (1 / 2 : ℝ) - η R) atTop (nhds (1 / 2)) := by
      simpa using (tendsto_const_nhds (x := (1 / 2 : ℝ))).sub hη_tend
    exact le_of_tendsto htend_lhs
      (eventually_ge_atTop (max 1 (|s₁Star + 1| + 1)) |>.mono fun R hR => hR_bd R hR)
  have hΨ_ne_zero : ∃ z : ℂ, Ψ z ≠ 0 := by
    by_contra h0
    push Not at h0
    have hz : ∫ s : ℝ, max 0 (-(Ψ (s : ℂ)).re) = 0 := by
      simp [h0]
    linarith
  -- Step 8: (vi) `f(u) = Ψ (-u / β)` properties + order `≤ 3/2`.
  let f : ℂ → ℂ := fun u => Ψ (-u / (betaTip : ℂ))
  have hf_diff : Differentiable ℂ f :=
    hΨ_diff.comp ((differentiable_id.neg).div_const _)
  have hCf_pull : ∃ C_f : ℝ, 0 ≤ C_f ∧ ∀ u : ℂ, ‖f u‖ ≤ C_f * (1 + ‖u‖) ^ (1 / 2 : ℝ) * airyEnv u := by
    let K_f : ℝ := max 1 betaTip⁻¹
    have hKf_pos : 0 < K_f := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    refine ⟨C_env * K_f ^ (1 / 2 : ℝ), by positivity, fun u => ?_⟩
    have hbu := hΨ_i1 (-u / (betaTip : ℂ))
    have hb0 : (betaTip : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr betaTip_pos.ne'
    rw [show -(betaTip : ℂ) * (-u / (betaTip : ℂ)) = u by field_simp] at hbu
    have hnorm_s : ‖-u / (betaTip : ℂ)‖ = ‖u‖ * betaTip⁻¹ := by
      rw [norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos betaTip_pos,
        div_eq_mul_inv]
    have hlin : 1 + ‖-u / (betaTip : ℂ)‖ ≤ K_f * (1 + ‖u‖) := by
      rw [hnorm_s]; have : betaTip⁻¹ ≤ K_f := le_max_right _ _
      nlinarith [norm_nonneg u, le_max_left 1 betaTip⁻¹]
    have hp : (1 + ‖-u / (betaTip : ℂ)‖) ^ (1 / 2 : ℝ) ≤ K_f ^ (1 / 2 : ℝ) * (1 + ‖u‖) ^ (1 / 2 : ℝ) :=
      (Real.rpow_le_rpow (by linarith [norm_nonneg (-u / (betaTip : ℂ))]) hlin (by norm_num)).trans_eq
        (Real.mul_rpow hKf_pos.le (by linarith [norm_nonneg u]))
    calc ‖f u‖ ≤ C_env * (1 + ‖-u / (betaTip : ℂ)‖) ^ (1 / 2 : ℝ) * airyEnv u := hbu
      _ ≤ C_env * (K_f ^ (1 / 2 : ℝ) * (1 + ‖u‖) ^ (1 / 2 : ℝ)) * airyEnv u := by
          gcongr; exact (airyEnv_pos u).le
      _ = (C_env * K_f ^ (1 / 2 : ℝ)) * (1 + ‖u‖) ^ (1 / 2 : ℝ) * airyEnv u := by ring
  obtain ⟨C_f, hCf_nn, hf_bd⟩ := hCf_pull
  have hf_int : Integrable (fun u : ℝ => f (u : ℂ)) := by
    have hfc : ∀ u : ℝ, f (u : ℂ) = Ψ (((-betaTip⁻¹ * u : ℝ) : ℂ)) := fun u => by
      dsimp [f]; push_cast; ring_nf
    simp_rw [hfc]
    exact hΨ_int.comp_mul_left' (neg_ne_zero.mpr (inv_ne_zero betaTip_pos.ne'))
  have hf_ne_zero : ∃ u : ℂ, f u ≠ 0 := by
    obtain ⟨z, hz⟩ := hΨ_ne_zero
    refine ⟨-(betaTip : ℂ) * z, ?_⟩
    dsimp [f]
    rwa [show -(-(betaTip : ℂ) * z) / (betaTip : ℂ) = z by
      have hβ : (betaTip : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr betaTip_pos.ne'
      field_simp [hβ]]
  have hf_im : ∀ u : ℝ, (f (u : ℂ)).im = 0 := fun u => by
    dsimp [f]
    rw [show -((u : ℂ)) / (betaTip : ℂ) = (((-u / betaTip : ℝ) : ℂ)) by push_cast; ring]
    exact hΨ_im _
  have hf_nonneg : ∀ u : ℝ, u ≤ -betaTip * s₁Star → 0 ≤ (f (u : ℂ)).re := fun u hu => by
    dsimp [f]
    rw [show -((u : ℂ)) / (betaTip : ℂ) = (((-u / betaTip : ℝ) : ℂ)) by push_cast; ring]
    refine hΨ_nonneg _ ?_
    rw [le_div_iff₀ betaTip_pos]
    linarith
  have hf_int_re : ∫ u : ℝ, (f (u : ℂ)).re ≤ 0 := by
    have hsc : ∀ u : ℝ, (f (u : ℂ)).re = (fun s : ℝ => (Ψ (s : ℂ)).re) ((-(betaTip⁻¹)) * u) := fun u => by
      dsimp [f]; congr 2; push_cast; ring
    have hcov := Measure.integral_comp_mul_left (fun s : ℝ => (Ψ (s : ℂ)).re) (-(betaTip⁻¹))
    have h_eq : (fun u : ℝ => (f (u : ℂ)).re) =
        (fun u : ℝ => (fun s : ℝ => (Ψ (s : ℂ)).re) ((-(betaTip⁻¹)) * u)) :=
      funext hsc
    rw [h_eq, hcov, smul_eq_mul]
    have hpref : 0 ≤ |(-(betaTip⁻¹))⁻¹| := abs_nonneg _
    calc |(-(betaTip⁻¹))⁻¹| * ∫ x : ℝ, (Ψ (x : ℂ)).re
        = |(-(betaTip⁻¹))⁻¹| * -(γLim + mEsc) := by rw [hre_eq]
      _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hpref (by linarith)
  have hΨ_ord : ∀ ε : ℝ, 0 < ε → ∃ C_ord : ℝ, 0 ≤ C_ord ∧
      ∀ ζ : ℂ, ‖Ψ ζ‖ ≤ C_ord * Real.exp ((KTip + ε) * ‖ζ‖ ^ (3 / 2 : ℝ)) := by
    intro ε hε
    let R₀ : ℝ := max 1 (ε⁻¹ ^ 2)
    let C_ord : ℝ := C_env * (1 + R₀)
    have hR₀_nn : 0 ≤ R₀ := by positivity
    refine ⟨C_ord, mul_nonneg hCenv_nn (by positivity), fun ζ => ?_⟩
    have h1 : ‖Ψ ζ‖ ≤ C_env * (1 + ‖ζ‖) ^ (1 / 2 : ℝ) * Real.exp (KTip * ‖ζ‖ ^ (3 / 2 : ℝ)) := by
      have hH := Real.exp_le_exp.mpr (hΨ_pt ζ)
      have hi1 := hΨ_i1 ζ
      rw [← tipH_eq_airyEnv ζ] at hi1
      exact hi1.trans (mul_le_mul_of_nonneg_left hH (by positivity))
    have hpoly : (1 + ‖ζ‖) ^ (1 / 2 : ℝ) ≤ (1 + R₀) * Real.exp (ε * ‖ζ‖ ^ (3 / 2 : ℝ)) := by
      rcases le_or_gt ‖ζ‖ R₀ with hle | hgt
      · have hsqrt : (1 + ‖ζ‖) ^ (1 / 2 : ℝ) ≤ 1 + ‖ζ‖ := by
          calc (1 + ‖ζ‖) ^ (1 / 2 : ℝ) ≤ (1 + ‖ζ‖) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg ζ]) (by norm_num)
            _ = 1 + ‖ζ‖ := Real.rpow_one _
        have hexp_ge1 : 1 ≤ Real.exp (ε * ‖ζ‖ ^ (3 / 2 : ℝ)) :=
          Real.one_le_exp (by positivity)
        calc (1 + ‖ζ‖) ^ (1 / 2 : ℝ) ≤ 1 + R₀ := by linarith
          _ = (1 + R₀) * 1 := (mul_one _).symm
          _ ≤ (1 + R₀) * Real.exp (ε * ‖ζ‖ ^ (3 / 2 : ℝ)) :=
              mul_le_mul_of_nonneg_left hexp_ge1 (by positivity)
      · have hr_ge1 : 1 ≤ ‖ζ‖ := (le_max_left 1 (ε⁻¹ ^ 2)).trans hgt.le
        have hr_le : ‖ζ‖ ≤ ε * ‖ζ‖ ^ (3 / 2 : ℝ) := by
          have hpow : ‖ζ‖ ^ (1 / 2 : ℝ) * ‖ζ‖ = ‖ζ‖ ^ (3 / 2 : ℝ) := by
            conv_lhs => arg 2; rw [← Real.rpow_one ‖ζ‖]
            rw [← Real.rpow_add (by linarith)]; norm_num
          have hεr : 1 ≤ ε * ‖ζ‖ ^ (1 / 2 : ℝ) := by
            have hsq : (ε⁻¹) ^ 2 ≤ ‖ζ‖ := (le_max_right 1 (ε⁻¹ ^ 2)).trans hgt.le
            have hhalf : ε⁻¹ ≤ ‖ζ‖ ^ (1 / 2 : ℝ) := by
              rw [← Real.sqrt_sq (inv_nonneg.mpr hε.le), Real.sqrt_eq_rpow]
              exact Real.rpow_le_rpow (by positivity) hsq (by norm_num)
            calc 1 = ε * ε⁻¹ := (mul_inv_cancel₀ hε.ne').symm
              _ ≤ ε * ‖ζ‖ ^ (1 / 2 : ℝ) := mul_le_mul_of_nonneg_left hhalf hε.le
          calc ‖ζ‖ = 1 * ‖ζ‖ := (one_mul _).symm
            _ ≤ (ε * ‖ζ‖ ^ (1 / 2 : ℝ)) * ‖ζ‖ :=
                mul_le_mul_of_nonneg_right hεr (norm_nonneg ζ)
            _ = ε * (‖ζ‖ ^ (1 / 2 : ℝ) * ‖ζ‖) := by ring
            _ = ε * ‖ζ‖ ^ (3 / 2 : ℝ) := by rw [hpow]
        have hsqrt : (1 + ‖ζ‖) ^ (1 / 2 : ℝ) ≤ 1 + ‖ζ‖ := by
          calc (1 + ‖ζ‖) ^ (1 / 2 : ℝ) ≤ (1 + ‖ζ‖) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg ζ]) (by norm_num)
            _ = 1 + ‖ζ‖ := Real.rpow_one _
        have hexp_ge : 1 + ε * ‖ζ‖ ^ (3 / 2 : ℝ) ≤ Real.exp (ε * ‖ζ‖ ^ (3 / 2 : ℝ)) := by
          linarith [Real.add_one_le_exp (ε * ‖ζ‖ ^ (3 / 2 : ℝ))]
        calc (1 + ‖ζ‖) ^ (1 / 2 : ℝ) ≤ 1 + ‖ζ‖ := hsqrt
          _ ≤ 1 + ε * ‖ζ‖ ^ (3 / 2 : ℝ) := by linarith
          _ ≤ Real.exp (ε * ‖ζ‖ ^ (3 / 2 : ℝ)) := hexp_ge
          _ = 1 * Real.exp (ε * ‖ζ‖ ^ (3 / 2 : ℝ)) := (one_mul _).symm
          _ ≤ (1 + R₀) * Real.exp (ε * ‖ζ‖ ^ (3 / 2 : ℝ)) :=
              mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
    calc ‖Ψ ζ‖
        ≤ C_env * (1 + ‖ζ‖) ^ (1 / 2 : ℝ) * Real.exp (KTip * ‖ζ‖ ^ (3 / 2 : ℝ)) := h1
      _ ≤ C_env * ((1 + R₀) * Real.exp (ε * ‖ζ‖ ^ (3 / 2 : ℝ))) *
            Real.exp (KTip * ‖ζ‖ ^ (3 / 2 : ℝ)) := by gcongr
      _ = C_ord * (Real.exp (KTip * ‖ζ‖ ^ (3 / 2 : ℝ)) * Real.exp (ε * ‖ζ‖ ^ (3 / 2 : ℝ))) := by
            dsimp [C_ord]; ring
      _ = C_ord * Real.exp ((KTip + ε) * ‖ζ‖ ^ (3 / 2 : ℝ)) := by
            rw [← Real.exp_add]; congr 2; ring
  exact ⟨ms, s₁Star, Ψ, γLim, mEsc, C_env, hms_strict, hs₁_sub, hΨ_lim, hγ_sub, hΨ_diff,
    hCenv_nn, hΨ_i1, hΨ_i2, hΨ_i3, hΨ_int, hΨ_norm_le, hΨ_im, hΨ_nonneg, hγLim_nn, hmEsc_nn,
    hre_eq, hneg_half, hΨ_ne_zero, hf_diff, ⟨C_f, hCf_nn, hf_bd⟩, hf_int, hf_ne_zero, hf_im,
    hf_nonneg, hf_int_re, hΨ_ord⟩

/-! ### Section 5: Discharging `BlowupFamilyPackage`, `RigidityFamilyPackage`, and Theorems C, R1--R3 -/

/-- Construct a `BlowupFamilyPackage ι p` from any family of concrete `BlowupTest inp (c' n)`
with `Tendsto c' p atTop`, discharging `propT_subseq` and `theorem_A_lower`. -/
noncomputable def blowupFamilyPackage_of_tests {ι : Type*} {p : Filter ι}
    (hI0 : BesselI0Asymptotic) (inp : StripBootstrapInputs)
    {c' : ι → ℝ} (hc' : Tendsto c' p atTop)
    (tests : ∀ n : ι, BlowupTest inp (c' n)) :
    BlowupFamilyPackage ι p where
  c' := c'
  s₁ := fun n => tipS₁ (c' n) (tests n)
  t₁ := fun n => (tests n).t₁
  Φ := fun n => tipRescale (c' n) (tests n)
  γ := fun n => (tests n).gVac / (2 * π * (tests n).M)
  hc'_tendsto := hc'
  hγ_nonneg := Eventually.of_forall fun n =>
    div_nonneg (tests n).hgVac_nonneg (by positivity [Real.pi_pos, (tests n).hM_pos])
  scaling_eq := by
    filter_upwards [hc'.eventually (eventually_gt_atTop (0 : ℝ))] with n hc'n
    exact tipS₁_scaling_eq hc'n (tests n)
  theorem_A_lower := by
    obtain ⟨C₀, c_A, _, _, hA⟩ := tipS₁_theorem_A_lower inp
    refine ⟨C₀, ?_⟩
    filter_upwards [hc'.eventually (eventually_ge_atTop c_A)] with n hc'n
    exact hA hc'n (tests n)
  propT_subseq := fun ns hns hB => by
    obtain ⟨ms, s₁Star, Ψ, γLim, mEsc, C_env, hms, hs₁, hΦ, hγ, hΨd, hCnn, hΨb, _, _, hΨi,
      hΨnorm, hΨim, hΨnn, hγnn, hmEscnn, hΨre, hneg, hΨne, _⟩ :=
      proposition_T hI0 inp (hc'.comp hns) (fun k => tests (ns k)) hB
    exact ⟨ms, s₁Star, Ψ, γLim, mEsc, hms, hs₁, hΦ, hγ, hΨd, hΨi, ⟨C_env, hCnn, hΨb⟩, hΨne,
      hΨim, hΨnn, hΨnorm, hγnn, hmEscnn, hΨre, hneg⟩

/-- If `g : ℝ → ℝ` is continuous on `[0, ∞)` and `t₁` is the minimal nonnegative threshold
`sInf {T ≥ 0 | ∀ t ≥ T, 0 ≤ g t}` with `0 < t₁`, then `g t₁ = 0` (`rigidity.tex`). -/
theorem isThreshold_imp_g_t1_eq_zero {g : ℝ → ℝ} {t₁ : ℝ}
    (hg_cont : ContinuousOn g (Ici 0)) (ht₁_pos : 0 < t₁)
    (ht₁_eq : t₁ = sInf {T : ℝ | 0 ≤ T ∧ ∀ t : ℝ, T ≤ t → 0 ≤ g t})
    (hnonneg : ∀ t : ℝ, t₁ ≤ t → 0 ≤ g t) :
    g t₁ = 0 := by
  by_contra hne
  have hge0 : 0 ≤ g t₁ := hnonneg t₁ le_rfl
  have hgt0 : 0 < g t₁ := lt_of_le_of_ne hge0 (Ne.symm hne)
  have hcont_at : ContinuousAt g t₁ :=
    hg_cont.continuousAt (Ici_mem_nhds ht₁_pos)
  obtain ⟨δ, hδ_pos, hδ_ball⟩ := Metric.mem_nhds_iff.mp
    (hcont_at.eventually (eventually_gt_nhds (by linarith : (0 : ℝ) < g t₁)))
  let T' : ℝ := max 0 (t₁ - δ / 2)
  have hT'_lt : T' < t₁ := max_lt ht₁_pos (by linarith)
  have hT'_mem : T' ∈ {T : ℝ | 0 ≤ T ∧ ∀ t : ℝ, T ≤ t → 0 ≤ g t} := by
    refine ⟨le_max_left _ _, fun t ht => ?_⟩
    rcases le_or_gt t₁ t with h1 | h1
    · exact hnonneg t h1
    · have hdist : t ∈ ball t₁ δ := by
        rw [mem_ball, Real.dist_eq, abs_lt]
        have hT'_ge : t₁ - δ / 2 ≤ T' := le_max_right _ _
        constructor <;> linarith
      exact (hδ_ball hdist).le
  have hle : t₁ ≤ T' := by
    rw [ht₁_eq]
    exact csInf_le ⟨0, fun _ hT => hT.1⟩ hT'_mem
  linarith

/-- Construct a full `RigidityFamilyPackage ι p` from a family of `BlowupTest`s
(deriving `0 < t₁ → g t₁ = 0` from `ht₁_least` via `isThreshold_imp_g_t1_eq_zero`). -/
noncomputable def rigidityFamilyPackage_of_tests {ι : Type*} {p : Filter ι}
    (hI0 : BesselI0Asymptotic) (inp : StripBootstrapInputs)
    {c' : ι → ℝ} (hc' : Tendsto c' p atTop)
    (tests : ∀ n : ι, BlowupTest inp (c' n)) :
    RigidityFamilyPackage ι p where
  toBlowupFamilyPackage := blowupFamilyPackage_of_tests hI0 inp hc' tests
  domain_integrable := by
    filter_upwards [hc'.eventually (eventually_gt_atTop (0 : ℝ))] with n hc'n
    dsimp [blowupFamilyPackage_of_tests]
    simpa only [tipSMin] using tipRescale_integrableOn_domain hc'n (tests n)
  domain_norm_integral := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hc'.eventually (eventually_gt_atTop (0 : ℝ))] with n hc'n
    dsimp [blowupFamilyPackage_of_tests]
    simpa only [tipSMin] using (tipRescale_norm_integral hc'n (tests n)).symm
  holo_balls := fun R => by
    have hεR : Tendsto (fun n => 2 * R * tipEps (c' n)) p (nhds 0) := by
      have h0 := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp hc'
      simpa [tipEps] using h0.const_mul (2 * R)
    filter_upwards [hc'.eventually (eventually_gt_atTop (0 : ℝ)),
      hεR.eventually (eventually_lt_nhds one_pos)] with n hc'n h2R
    dsimp [blowupFamilyPackage_of_tests]
    exact tipRescale_holo_ball hc'n h2R (tests n)
  real_symm := fun R => by
    have hεR : Tendsto (fun n => 2 * R * tipEps (c' n)) p (nhds 0) := by
      have h0 := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp hc'
      simpa [tipEps] using h0.const_mul (2 * R)
    filter_upwards [hc'.eventually (eventually_gt_atTop (0 : ℝ)),
      hεR.eventually (eventually_lt_nhds one_pos)] with n hc'n h2R z hz
    have hε_pos := tipEps_pos hc'n
    have him : |z.im| < 1 / (2 * tipEps (c' n)) := by
      have hzn : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
      have hzr : ‖z‖ < R := mem_ball_zero_iff.mp hz
      rw [lt_div_iff₀ (by positivity)]
      nlinarith
    dsimp [blowupFamilyPackage_of_tests]
    exact tipRescale_real_symm hc'n (tests n) him
  nonneg_tail := by
    filter_upwards [hc'.eventually (eventually_gt_atTop (0 : ℝ))] with n hc'n s hs
    dsimp [blowupFamilyPackage_of_tests] at hs ⊢
    exact tipRescale_nonneg_tail hc'n (tests n) s hs
  s1_is_zero := by
    obtain ⟨C_A, c_A, _, hcA_ge1, hA⟩ := theorem_A inp.pj inp.fg
    have hpos_t1 : Tendsto (fun n => xiBar * c' n - C_A * c' n ^ (1 / 3 : ℝ)) p atTop := by
      have hsub : ∀ᶠ n in p, 1 ≤ c' n →
          xiBar * c' n - C_A * c' n ^ (1 / 3 : ℝ) =
            c' n * (xiBar - C_A * c' n ^ (-(2 / 3 : ℝ))) := by
        filter_upwards [hc'.eventually (eventually_ge_atTop (1 : ℝ))] with n hc'1 _
        have hc'n : 0 < c' n := by linarith
        have h1 : c' n * c' n ^ (-(2 / 3 : ℝ)) = c' n ^ (1 / 3 : ℝ) := by
          conv_lhs => arg 1; rw [← Real.rpow_one (c' n)]
          rw [← Real.rpow_add hc'n]; norm_num
        linarith [show C_A * (c' n * c' n ^ (-(2 / 3 : ℝ))) = C_A * c' n ^ (1 / 3 : ℝ) by rw [h1]]
      have hfac : Tendsto (fun n => c' n * (xiBar - C_A * c' n ^ (-(2 / 3 : ℝ)))) p atTop := by
        have hlim : Tendsto (fun n => xiBar - C_A * c' n ^ (-(2 / 3 : ℝ))) p (nhds xiBar) := by
          have h0 := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp hc').const_mul C_A
          simpa using tendsto_const_nhds.sub h0
        have hxi_pos : 0 < xiBar := by unfold xiBar; positivity [xiStar_pos]
        exact hc'.atTop_mul_pos hxi_pos hlim
      refine hfac.congr' ?_
      filter_upwards [hc'.eventually (eventually_ge_atTop (1 : ℝ)), hsub] with n hn hs
      exact (hs hn).symm
    filter_upwards [hc'.eventually (eventually_ge_atTop c_A),
      hpos_t1.eventually (eventually_gt_atTop (0 : ℝ))] with n hc'n hlb
    have hc'0 : 0 < c' n := lt_of_lt_of_le (by linarith) hc'n
    have ht1_pos : 0 < (tests n).t₁ :=
      lt_of_lt_of_le hlb (hA hc'n ((tests n).toWeaklyFeasibleTest hc'0.le))
    have hg0 : (tests n).g (tests n).t₁ = 0 :=
      isThreshold_imp_g_t1_eq_zero (tests n).hg_cont ht1_pos (tests n).ht₁_least
        (tests n).hg_nonneg_tail
    have ht_eq : tipTReal (c' n) (tipS₁ (c' n) (tests n)) = (tests n).t₁ := by
      unfold tipTReal tipBReal tipS₁
      have hε : tipEps (c' n) ≠ 0 := (tipEps_pos hc'0).ne'
      rw [show xiStar + tipEps (c' n) * (((tests n).x₁ - xiStar) / tipEps (c' n)) = (tests n).x₁ by
        field_simp [hε]; ring, ← (tests n).ht₁_eq]
    dsimp [blowupFamilyPackage_of_tests]
    rw [tipRescale_real_on_real, ht_eq, hg0]
    simp

/-- **Theorem C** (`local_airy_model.tex`) applied directly to a family of `BlowupTest`s. -/
theorem blowup_theorem_C {ι : Type*} {p : Filter ι} [p.NeBot] [p.IsCountablyGenerated]
    (hI0 : BesselI0Asymptotic) (inp : StripBootstrapInputs)
    {c' : ι → ℝ} (hc' : Tendsto c' p atTop) (tests : ∀ n : ι, BlowupTest inp (c' n)) :
    (Aopt : EReal) ≤
      Filter.liminf (fun n =>
        ((((tests n).t₁ - xiBar * c' n) / (c' n) ^ (1 / 3 : ℝ) : ℝ) : EReal)) p :=
  theorem_C (blowupFamilyPackage_of_tests hI0 inp hc' tests)

/-- **Theorem R `(R1)`** (`rigidity.tex`) applied directly to a family of `BlowupTest`s. -/
theorem blowup_theorem_R1 {ι : Type*} {p : Filter ι} [p.IsCountablyGenerated]
    (hI0 : BesselI0Asymptotic) (inp : StripBootstrapInputs)
    {c' : ι → ℝ} (hc' : Tendsto c' p atTop) (tests : ∀ n : ι, BlowupTest inp (c' n))
    (hAtt : Att (blowupFamilyPackage_of_tests hI0 inp hc' tests)) :
    Tendsto (fun n => tipS₁ (c' n) (tests n)) p (nhds s1) ∧
    TendstoLocallyUniformlyOn (fun n => tipRescale (c' n) (tests n)) phiStar p univ ∧
    Tendsto (fun n => (tests n).gVac / (2 * π * (tests n).M)) p (nhds 0) :=
  theorem_R1 (blowupFamilyPackage_of_tests hI0 inp hc' tests) hAtt

/-- **Theorem R `(R2)`** (`rigidity.tex`) applied directly to a family of `BlowupTest`s. -/
theorem blowup_theorem_R2 {ι : Type*} {p : Filter ι} [p.NeBot] [p.IsCountablyGenerated]
    (hI0 : BesselI0Asymptotic) (inp : StripBootstrapInputs)
    {c' : ι → ℝ} (hc' : Tendsto c' p atTop) (tests : ∀ n : ι, BlowupTest inp (c' n))
    (hAtt : Att (blowupFamilyPackage_of_tests hI0 inp hc' tests)) :
    let R := rigidityFamilyPackage_of_tests hI0 inp hc' tests
    Tendsto (fun n => ∫ s : ℝ, ‖phiExt R n s - phiStar (s : ℂ)‖) p (nhds 0) ∧
    (∀ ε : ℝ, 0 < ε → ∃ R₀ : ℝ, 0 < R₀ ∧
      ∀ᶠ n in p, ∫ s in Ioi R₀ ∪ Iio (-R₀), ‖phiExt R n s‖ < ε) ∧
    Tendsto (fun R₀ : ℝ => Filter.limsup (fun n => ∫ s in Ioi R₀ ∪ Iio (-R₀), ‖phiExt R n s‖) p)
      atTop (nhds 0) := by
  intro R
  have hR := theorem_R2 R hAtt
  exact ⟨hR.1, hR.2.2.1, hR.2.2.2⟩

/-- **Theorem R `(R3)`** (`rigidity.tex`) applied directly to a family of `BlowupTest`s. -/
theorem blowup_theorem_R3 {ι : Type*} {p : Filter ι} [p.NeBot] [p.IsCountablyGenerated]
    (hI0 : BesselI0Asymptotic) (inp : StripBootstrapInputs)
    {c' : ι → ℝ} (hc' : Tendsto c' p atTop) (tests : ∀ n : ι, BlowupTest inp (c' n))
    (hAtt : Att (blowupFamilyPackage_of_tests hI0 inp hc' tests)) :
    let R := rigidityFamilyPackage_of_tests hI0 inp hc' tests
    (∃ r₀ > 0, ∀ r, 0 < r → r ≤ r₀ → ∀ᶠ n in p,
      zeroCount (R.Φ n) (s1 : ℂ) r = 1 ∧ (R.s₁ n : ℂ) ∈ ball (s1 : ℂ) r ∧
      R.Φ n (R.s₁ n : ℂ) = 0 ∧ analyticOrderNatAt (R.Φ n) (R.s₁ n : ℂ) = 1 ∧
      ∀ z ∈ ball (s1 : ℂ) r, R.Φ n z = 0 → z = (R.s₁ n : ℂ)) ∧
    (∀ k : ℕ, 2 ≤ k → ∃ r₀ > 0,
      (∀ r, 0 < r → r ≤ r₀ → ∀ᶠ n in p,
        zeroCount (R.Φ n) (sNode k : ℂ) r = 2 ∧
        ((∃ x : ℝ, (x : ℂ) ∈ ball (sNode k : ℂ) r ∧ R.Φ n (x : ℂ) = 0 ∧
            analyticOrderNatAt (R.Φ n) (x : ℂ) = 2 ∧
            ∀ z ∈ ball (sNode k : ℂ) r, R.Φ n z = 0 → z = (x : ℂ)) ∨
         (∃ z : ℂ, z ∈ ball (sNode k : ℂ) r ∧ z.im ≠ 0 ∧ R.Φ n z = 0 ∧
            R.Φ n (starRingEnd ℂ z) = 0 ∧ analyticOrderNatAt (R.Φ n) z = 1 ∧
            analyticOrderNatAt (R.Φ n) (starRingEnd ℂ z) = 1 ∧
            ∀ w ∈ ball (sNode k : ℂ) r, R.Φ n w = 0 → w = z ∨ w = starRingEnd ℂ z))) ∧
      (∀ z : ι → ℂ, (∀ᶠ n in p, z n ∈ ball (sNode k : ℂ) r₀ ∧ R.Φ n (z n) = 0) →
        Tendsto z p (nhds (sNode k : ℂ)) ∧
        Tendsto (fun n => (tScale (R.c' n) (z n) - ((xiBar * R.c' n : ℝ) : ℂ)) /
            (((R.c' n) ^ (1 / 3 : ℝ) : ℝ) : ℂ)) p
          (nhds ((((|airyZero k| / |airyZero 1|) * Aopt : ℝ) : ℂ))) ∧
        (k = 2 →
          Tendsto (fun n => (tScale (R.c' n) (z n) - (R.t₁ n : ℂ)) /
              ((((R.c' n + 1) ^ (1 / 3 : ℝ) : ℝ) : ℂ))) p
            (nhds ((((|airyZero 2| / |airyZero 1| - 1) * Aopt : ℝ) : ℂ))))) ∧
      (∃ z : ι → ℂ, ∀ᶠ n in p, z n ∈ ball (sNode k : ℂ) r₀ ∧ R.Φ n (z n) = 0)) ∧
    (∀ K : Set ℂ, IsCompact K → (∀ k : ℕ, 1 ≤ k → (sNode k : ℂ) ∉ K) →
      ∀ᶠ n in p, ∀ z ∈ K, R.Φ n z ≠ 0) :=
  theorem_R3 _ hAtt

end FormalResearch.ModularBootstrap

section AxiomChecks
open FormalResearch.ModularBootstrap

/-- info: 'FormalResearch.ModularBootstrap.tipRescale_pointwise_envelope' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tipRescale_pointwise_envelope

/-- info: 'FormalResearch.ModularBootstrap.montel_exhaustion_entire' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms montel_exhaustion_entire

/-- info: 'FormalResearch.ModularBootstrap.blowup_left_tail_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms blowup_left_tail_bound

/-- info: 'FormalResearch.ModularBootstrap.tipS₁_theorem_A_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tipS₁_theorem_A_lower

/-- info: 'FormalResearch.ModularBootstrap.proposition_T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms proposition_T

/-- info: 'FormalResearch.ModularBootstrap.blowupFamilyPackage_of_tests' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms blowupFamilyPackage_of_tests

/-- info: 'FormalResearch.ModularBootstrap.isThreshold_imp_g_t1_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isThreshold_imp_g_t1_eq_zero

/-- info: 'FormalResearch.ModularBootstrap.rigidityFamilyPackage_of_tests' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rigidityFamilyPackage_of_tests

/-- info: 'FormalResearch.ModularBootstrap.blowup_theorem_C' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms blowup_theorem_C

/-- info: 'FormalResearch.ModularBootstrap.blowup_theorem_R1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms blowup_theorem_R1

/-- info: 'FormalResearch.ModularBootstrap.blowup_theorem_R2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms blowup_theorem_R2

/-- info: 'FormalResearch.ModularBootstrap.blowup_theorem_R3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms blowup_theorem_R3

end AxiomChecks
