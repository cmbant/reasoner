module

public import FormalResearch.ModularBootstrap.Spin.SpinS4_4_1
public import FormalResearch.ModularBootstrap.Spin.SpinS4_4_2_Strip
public import FormalResearch.ModularBootstrap.Spin.SpinS4_4_2_Slit
public import FormalResearch.ModularBootstrap.Spin.SpinS4_4_2_StripCont
public import FormalResearch.ModularBootstrap.TipFront.ComplexPoissonJensen
public import FormalResearch.ModularBootstrap.TipFront.ComplexMajorant
public import FormalResearch.ModularBootstrap.Blowup.Majorant

public import FormalResearch.ModularBootstrap.Spin.SpinS4_4_2_PJ
/-!
# SPIN-S4 Lemma 4.2 (`s4:4.2`, `spinning_s4.tex`)

Proves `spinS4_4_2 : SpinS4_4_2`: for each `V > 0` and `R > 0`, there exist `C_RV > 0` and
`c₀ ≥ 40` such that for all `c ≥ c₀`, `Φ ∈ SpinTestClass ((c - 1) / 12)` with `spinM2 = 1`, and
all measurable selectors `0 ≤ χ ≤ 1` supported in `[-V, V]`, `spinHProfile c N Φ χ` is
holomorphic on `closedBall (0 : ℂ) R` and bounded in norm by `C_RV`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real ENNReal

namespace FormalResearch.ModularBootstrap.Spin

open FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.PoissonJensen
open FormalResearch.Special

private lemma spinS4_4_2_finish {w₀ : ℂ} {R C_pj : ℝ} {f_sub : ℂ → ℂ}
    (hR : 0 < R) (hw₀_norm : ‖w₀‖ ≤ 2 * R + 1 / 2)
    (han_disc : AnalyticOnNhd ℂ f_sub (closedBall w₀ (1 / 2 * (1 + ‖w₀‖) ^ (-(1 / 2 : ℝ)))))
    (hf_sub_ne : f_sub w₀ ≠ 0)
    (hB_ae : ∀ᵐ w ∂(volume.restrict (ball w₀ (1 / 2 * (1 + ‖w₀‖) ^ (-(1 / 2 : ℝ))))),
      Real.log ‖f_sub w‖ ≤ (C_pj + tipH w₀ + 3 * KTip / 4) - Real.log (tipDist w)) :
    ‖f_sub w₀‖ ≤ Real.exp (C_pj + KTip * (2 * R + 1) ^ (3 / 2 : ℝ) + 3 * KTip / 4 +
      (Real.log 2 + 1 / 2 * Real.log (2 * R + 2) + Real.log 2 + 4 / π)) := by
  let R_box : ℝ := 2 * R + 1
  let C_neg_log : ℝ := Real.log 2 + 1 / 2 * Real.log (2 * R + 2) + Real.log 2 + 4 / π
  let C_RV : ℝ := Real.exp (C_pj + KTip * R_box ^ (3 / 2 : ℝ) + 3 * KTip / 4 + C_neg_log)
  have hCRV_pos : 0 < C_RV := Real.exp_pos _
  let r_disc : ℝ := (1 / 2 : ℝ) * (1 + ‖w₀‖) ^ (-(1 / 2 : ℝ))
  have hr_pos : 0 < r_disc := by positivity
  let B_fn : ℂ → ℝ := fun w => (C_pj + tipH w₀ + 3 * KTip / 4) - Real.log (tipDist w)
  have hc_int : IntegrableOn (fun _ : ℂ => C_pj + tipH w₀ + 3 * KTip / 4) (ball w₀ r_disc) :=
    integrableOn_const (hs := measure_ball_lt_top.ne)
  have hdist_int : IntegrableOn (fun w : ℂ => -Real.log (tipDist w)) (ball w₀ r_disc) :=
    (disc_avg_neg_log_tipDist w₀).1
  have hB_int : IntegrableOn B_fn (ball w₀ r_disc) := hc_int.add hdist_int
  have havg := subharmonic_disc_avg_le hr_pos han_disc hf_sub_ne hB_int hB_ae
  have hball_vol_pos : 0 < π * r_disc ^ 2 := by positivity
  have hvol : volume.real (ball w₀ r_disc) = π * r_disc ^ 2 := by
    simp [Measure.real_def, Complex.volume_ball, hr_pos.le, mul_comm]
  have hB_eval : (π * r_disc ^ 2)⁻¹ * ∫ w in ball w₀ r_disc, B_fn w =
      (C_pj + tipH w₀ + 3 * KTip / 4) + (π * r_disc ^ 2)⁻¹ * ∫ w in ball w₀ r_disc, -Real.log (tipDist w) := by
    have hsub_eq : B_fn = fun w => (C_pj + tipH w₀ + 3 * KTip / 4) + (-Real.log (tipDist w)) :=
      funext fun _ => by dsimp [B_fn]; ring
    rw [hsub_eq, integral_add hc_int hdist_int, setIntegral_const, hvol, smul_eq_mul, mul_add,
      ← mul_assoc, inv_mul_cancel₀ hball_vol_pos.ne', one_mul]
  have hdist_avg : (π * r_disc ^ 2)⁻¹ * ∫ w in ball w₀ r_disc, -Real.log (tipDist w) ≤ C_neg_log := by
    have h1 := (disc_avg_neg_log_tipDist w₀).2.1
    have hr_log : Real.log (1 / r_disc) ≤ Real.log 2 + (1 / 2 : ℝ) * Real.log (2 * R + 2) := by
      have hinv : 1 / r_disc = 2 * (1 + ‖w₀‖) ^ (1 / 2 : ℝ) := by
        dsimp [r_disc]
        rw [one_div, mul_inv, ← Real.rpow_neg (by linarith [norm_nonneg w₀])]
        norm_num
      rw [hinv, Real.log_mul two_pos.ne' (Real.rpow_pos_of_pos (by linarith [norm_nonneg w₀]) _).ne',
        Real.log_rpow (by linarith [norm_nonneg w₀])]
      have hle : 1 + ‖w₀‖ ≤ 2 * R + 2 := by linarith only [hw₀_norm]
      have hlog := Real.log_le_log (by linarith [norm_nonneg w₀]) hle
      linarith only [hlog]
    dsimp [C_neg_log]; linarith only [h1, hr_log]
  have hH_w₀ : tipH w₀ ≤ KTip * R_box ^ (3 / 2 : ℝ) := by
    refine (tipH_le_KTip_norm w₀).trans ?_
    have hw₀_Rbox : ‖w₀‖ ≤ R_box := by dsimp [R_box]; linarith only [hw₀_norm]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hw₀_Rbox (by norm_num)) KTip_pos.le
  have hlog_final : Real.log ‖f_sub w₀‖ ≤ Real.log C_RV := by
    calc Real.log ‖f_sub w₀‖
        ≤ (π * r_disc ^ 2)⁻¹ * ∫ w in ball w₀ r_disc, B_fn w := havg
      _ = (C_pj + tipH w₀ + 3 * KTip / 4) +
            (π * r_disc ^ 2)⁻¹ * ∫ w in ball w₀ r_disc, -Real.log (tipDist w) := hB_eval
      _ ≤ (C_pj + KTip * R_box ^ (3 / 2 : ℝ) + 3 * KTip / 4) + C_neg_log :=
            add_le_add (by linarith only [hH_w₀]) hdist_avg
      _ = Real.log C_RV := by dsimp [C_RV]; rw [Real.log_exp]
  exact (Real.log_le_log_iff (norm_pos_iff.mpr hf_sub_ne) hCRV_pos).mp hlog_final

/-- **`s4:4.2` (`spinning_s4.tex`, Lemma 4.2): uniform adaptive transverse-slice normal family.** -/
theorem spinS4_4_2 : SpinS4_4_2 := by
  intro V hV R hR
  obtain ⟨C_r, C_V, c₄₁, hCr_pos, hCV_pos, hc₄₁_40, h41_all⟩ :=
    spinS4_4_1 (r₀ := xiStar / 4) (V := V) (by positivity [xiStar_pos]) hV
  obtain ⟨ρ₁, C_T1, _ψ, hρ1_pos, hCT1_nn, _hψ_an, _hψ0, _hψd, _hψr, hT1⟩ := lemma_T1
  obtain ⟨ρ₂, C_T2, hρ2_pos, hCT2_nn, hT2⟩ := lemma_T2 TipFront.lemmaGPotentialInput_virasoro
  have hT1_spec : ∀ {c' : ℝ} {ζ : ℂ}, 0 < c' → ¬ (ζ.im = 0 ∧ 0 ≤ ζ.re) →
      tipEps c' * ‖ζ‖ ≤ ρ₁ →
      ∃ z_b : ℂ, 0 < z_b.im ∧ ‖z_b - (sigmaStar : ℂ)‖ ≤ 0.1 ∧
        slitBoundaryMapC z_b = bScale c' ζ ∧
        |z_b.im - √(tipEps c' / slitQ) * ((-ζ) ^ (1 / 2 : ℂ)).re| ≤
          C_T1 * √(tipEps c' * ‖ζ‖) * (√(tipEps c' / slitQ) * ((-ζ) ^ (1 / 2 : ℂ)).re) ∧
        |z_b.im * ‖z_b - (sigmaStar : ℂ)‖ - (tipEps c' / slitQ) * tipDist ζ| ≤
          C_T1 * √(tipEps c' * ‖ζ‖) * ((tipEps c' / slitQ) * tipDist ζ) := by
    intro c' ζ hc' hζ hεζ
    have h := hT1 hc' hζ hεζ
    exact ⟨_, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩
  have hT2_spec : ∀ {c' : ℝ} {ζ : ℂ}, 0 < c' → ¬ (ζ.im = 0 ∧ 0 ≤ ζ.re) →
      tipEps c' * ‖ζ‖ ≤ ρ₂ →
      |c' * (majorant2D (bScale c' ζ) + (tipL (bScale c' ζ)).re) - tipH ζ| ≤
        C_T2 * tipEps c' * ‖ζ‖ ^ (5 / 2 : ℝ) := by
    intro c' ζ hc' hζ hεζ
    simpa [TipFront.lemmaGPotentialInput_virasoro_U] using (hT2 hc' hζ hεζ).2
  let R_box : ℝ := 2 * R + 1
  let B_slit : ℝ := max 1 (8 * C_r / spinSlitConst0)
  let C_pj : ℝ := Real.log 80 + Real.log B_slit + 1 + slitEntropyComplexConst + Real.log (2 * slitQ) + 2
  let C_neg_log : ℝ := Real.log 2 + (1 / 2 : ℝ) * Real.log (2 * R + 2) + Real.log 2 + 4 / π
  let C_RV : ℝ := Real.exp (C_pj + KTip * R_box ^ (3 / 2 : ℝ) + 3 * KTip / 4 + C_neg_log)
  have hCRV_pos : 0 < C_RV := Real.exp_pos _
  -- Tendsto-based threshold `c₀`
  have ht_log_div : ∀ p : ℝ, 0 < p → Tendsto (fun n : ℝ => Real.log n / n ^ p) atTop (𝓝 0) := fun p hp =>
    (isLittleO_log_rpow_atTop hp).tendsto_div_nhds_zero
  have ht_N_div : Tendsto (fun n : ℝ => (Nat.ceil (Real.log n) : ℝ) / n ^ (1 / 3 : ℝ)) atTop (𝓝 0) := by
    have ht0 : Tendsto (fun n : ℝ => (Real.log n + 1) / n ^ (1 / 3 : ℝ)) atTop (𝓝 0) := by
      have h1 := ht_log_div (1 / 3 : ℝ) (by norm_num)
      have h2 := tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)
      have heq : (fun n : ℝ => (Real.log n + 1) / n ^ (1 / 3 : ℝ)) =ᶠ[atTop]
          fun n => Real.log n / n ^ (1 / 3 : ℝ) + n ^ (-(1 / 3 : ℝ)) := by
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with n hn
        rw [add_div, Real.rpow_neg hn.le, ← one_div]
      exact ((h1.add h2).congr' heq.symm).trans (by simp)
    refine squeeze_zero' ?_ ?_ ht0
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with n hn; positivity
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with n hn
      have hlt : (Nat.ceil (Real.log n) : ℝ) ≤ Real.log n + 1 :=
        (Nat.ceil_lt_add_one (Real.log_nonneg hn)).le
      exact div_le_div_of_nonneg_right hlt (Real.rpow_nonneg (by linarith) _)
  have ht_N_n : Tendsto (fun n : ℝ => 768 * (Nat.ceil (Real.log n) : ℝ) / n) atTop (𝓝 0) := by
    have h0 : Tendsto (fun n : ℝ => ((Nat.ceil (Real.log n) : ℝ) / n ^ (1 / 3 : ℝ)) * (768 * n ^ (-(2 / 3 : ℝ))))
        atTop (𝓝 0) := by
      simpa using ht_N_div.mul ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).const_mul 768)
    refine h0.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with n hn
    rw [Real.rpow_neg hn.le]
    have hadd : n ^ (1 / 3 : ℝ) * n ^ (2 / 3 : ℝ) = n := by
      rw [← Real.rpow_add hn]; norm_num
    calc (Nat.ceil (Real.log n) : ℝ) / n ^ (1 / 3 : ℝ) * (768 * (n ^ (2 / 3 : ℝ))⁻¹)
        = 768 * (Nat.ceil (Real.log n) : ℝ) / (n ^ (1 / 3 : ℝ) * n ^ (2 / 3 : ℝ)) := by ring
      _ = 768 * (Nat.ceil (Real.log n) : ℝ) / n := by rw [hadd]
  have ht_Medge : Tendsto (fun n : ℝ =>
      16 * (2 * V * Real.sqrt (n ^ (-(2 / 3 : ℝ))) * C_V * (Nat.ceil (Real.log n) : ℝ) ^ 2))
      atTop (𝓝 0) := by
    have hN16 := ht_log_div (1 / 6 : ℝ) (by norm_num)
    have hN_sq : Tendsto (fun n : ℝ => (Nat.ceil (Real.log n) : ℝ) ^ 2 / n ^ (1 / 3 : ℝ)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℝ => ((Nat.ceil (Real.log n) : ℝ) / n ^ (1 / 6 : ℝ)) ^ 2) atTop (𝓝 0) := by
        have hbase : Tendsto (fun n : ℝ => (Nat.ceil (Real.log n) : ℝ) / n ^ (1 / 6 : ℝ)) atTop (𝓝 0) := by
          have ht0 : Tendsto (fun n : ℝ => (Real.log n + 1) / n ^ (1 / 6 : ℝ)) atTop (𝓝 0) := by
            have heq : (fun n : ℝ => (Real.log n + 1) / n ^ (1 / 6 : ℝ)) =ᶠ[atTop]
                fun n => Real.log n / n ^ (1 / 6 : ℝ) + n ^ (-(1 / 6 : ℝ)) := by
              filter_upwards [eventually_gt_atTop (0 : ℝ)] with n hn
              rw [add_div, Real.rpow_neg hn.le, ← one_div]
            exact ((hN16.add (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 6))).congr' heq.symm).trans
              (by simp)
          exact squeeze_zero'
            (eventually_ge_atTop (1 : ℝ) |>.mono fun n hn => by positivity)
            (eventually_ge_atTop (1 : ℝ) |>.mono fun n hn =>
              div_le_div_of_nonneg_right (Nat.ceil_lt_add_one (Real.log_nonneg hn)).le (by positivity))
            ht0
        simpa using hbase.pow 2
      refine h1.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with n hn
      rw [div_pow, ← Real.rpow_natCast (n ^ (1 / 6 : ℝ)) 2, ← Real.rpow_mul hn.le]; norm_num
    have hres : Tendsto (fun n : ℝ => (32 * V * C_V) * ((Nat.ceil (Real.log n) : ℝ) ^ 2 / n ^ (1 / 3 : ℝ)))
        atTop (𝓝 0) := by simpa using hN_sq.const_mul (32 * V * C_V)
    refine hres.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with n hn
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hn.le, show -(2 / 3 : ℝ) * (1 / 2 : ℝ) = -(1 / 3 : ℝ) by norm_num,
      Real.rpow_neg hn.le]
    ring
  have ht_eps : Tendsto (fun n : ℝ => n ^ (-(2 / 3 : ℝ))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)
  have ht_loga : Tendsto (fun n : ℝ =>
      (2 / (0.3 * π)) * ((3 / 2 : ℝ) * √(2 * n ^ (-(2 / 3 : ℝ)) / slitQ) * √R_box) * |Real.log (n / 12)|)
      atTop (𝓝 0) := by
    have ht1 : Tendsto (fun n : ℝ => |Real.log (n / 12)| / n ^ (1 / 3 : ℝ)) atTop (𝓝 0) := by
      have heq : (fun n : ℝ => |Real.log (n / 12)| / n ^ (1 / 3 : ℝ)) =ᶠ[atTop]
          fun n => (Real.log n - Real.log 12) / n ^ (1 / 3 : ℝ) := by
        filter_upwards [eventually_ge_atTop (12 : ℝ)] with n hn
        rw [Real.log_div (by linarith) (by norm_num), abs_of_nonneg]
        linarith [Real.log_le_log (by norm_num : (0 : ℝ) < 12) hn]
      have hsub : Tendsto (fun n : ℝ => Real.log n / n ^ (1 / 3 : ℝ) - Real.log 12 * n ^ (-(1 / 3 : ℝ)))
          atTop (𝓝 0) := by
        simpa using (ht_log_div (1 / 3 : ℝ) (by norm_num)).sub
          ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).const_mul (Real.log 12))
      have heq2 : (fun n : ℝ => Real.log n / n ^ (1 / 3 : ℝ) - Real.log 12 * n ^ (-(1 / 3 : ℝ))) =ᶠ[atTop]
          fun n => (Real.log n - Real.log 12) / n ^ (1 / 3 : ℝ) := by
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with n hn
        rw [sub_div, Real.rpow_neg hn.le]; ring
      exact hsub.congr' (heq2.trans heq.symm)
    let C_la : ℝ := (2 / (0.3 * π)) * ((3 / 2 : ℝ) * √(2 / slitQ) * √R_box)
    have hres : Tendsto (fun n : ℝ => C_la * (|Real.log (n / 12)| / n ^ (1 / 3 : ℝ))) atTop (𝓝 0) := by
      simpa using ht1.const_mul C_la
    refine hres.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with n hn
    rw [show 2 * n ^ (-(2 / 3 : ℝ)) / slitQ = (2 / slitQ) * n ^ (-(2 / 3 : ℝ)) by ring,
      Real.sqrt_mul (by positivity [slitQ_pos]), Real.sqrt_eq_rpow (n ^ (-(2 / 3 : ℝ))),
      ← Real.rpow_mul hn.le, show -(2 / 3 : ℝ) * (1 / 2 : ℝ) = -(1 / 3 : ℝ) by norm_num,
      Real.rpow_neg hn.le]
    dsimp [C_la]; ring
  have hev_n : ∀ᶠ n : ℝ in atTop,
      48 ≤ n ∧ c₄₁ - 1 ≤ n ∧
      768 * (Nat.ceil (Real.log n) : ℝ) / n ≤ 1 ∧
      n ^ (-(2 / 3 : ℝ)) * (2 * R + 3) < 1 / 4 ∧
      V * Real.sqrt (n ^ (-(2 / 3 : ℝ))) ≤ xiStar / 4 ∧
      16 * (2 * V * Real.sqrt (n ^ (-(2 / 3 : ℝ))) * C_V * (Nat.ceil (Real.log n) : ℝ) ^ 2) ≤ 1 ∧
      48 * (Nat.ceil (Real.log n) : ℝ) * xiStar / n ^ (1 / 3 : ℝ) ≤ 1 / 2 ∧
      (2 * n ^ (-(2 / 3 : ℝ))) * R_box ≤ min ρ₁ ρ₂ ∧
      C_T1 * √((2 * n ^ (-(2 / 3 : ℝ))) * R_box) ≤ 1 / 2 ∧
      C_T2 * (2 * n ^ (-(2 / 3 : ℝ))) * R_box ^ (5 / 2 : ℝ) ≤ 1 ∧
      (2 / (0.3 * π)) * ((3 / 2 : ℝ) * √(2 * n ^ (-(2 / 3 : ℝ)) / slitQ) * √R_box) * |Real.log (n / 12)| ≤ 1 := by
    have hN_delta : Tendsto (fun n : ℝ => 48 * xiStar * ((Nat.ceil (Real.log n) : ℝ) / n ^ (1 / 3 : ℝ)))
        atTop (𝓝 0) := by
      simpa using ht_N_div.const_mul (48 * xiStar)
    have hV_sqrt : Tendsto (fun n : ℝ => V * Real.sqrt (n ^ (-(2 / 3 : ℝ)))) atTop (𝓝 0) := by
      simpa using (ht_eps.sqrt.const_mul V)
    have he1 : ∀ᶠ n : ℝ in atTop, n ^ (-(2 / 3 : ℝ)) * (2 * R + 3) < 1 / 4 :=
      ((by simpa using ht_eps.mul_const (2 * R + 3) :
        Tendsto (fun n : ℝ => n ^ (-(2 / 3 : ℝ)) * (2 * R + 3)) atTop (𝓝 0))).eventually
        (gt_mem_nhds (by norm_num))
    have he2 : ∀ᶠ n : ℝ in atTop, V * Real.sqrt (n ^ (-(2 / 3 : ℝ))) ≤ xiStar / 4 :=
      (hV_sqrt.eventually (gt_mem_nhds (by positivity [xiStar_pos]))).mono fun _ h => h.le
    have he3 : ∀ᶠ n : ℝ in atTop, 48 * (Nat.ceil (Real.log n) : ℝ) * xiStar / n ^ (1 / 3 : ℝ) ≤ 1 / 2 :=
      ((hN_delta.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).mono fun n hn => by
        linarith [show 48 * (Nat.ceil (Real.log n) : ℝ) * xiStar / n ^ (1 / 3 : ℝ) =
          48 * xiStar * ((Nat.ceil (Real.log n) : ℝ) / n ^ (1 / 3 : ℝ)) by ring])
    have he4 : ∀ᶠ n : ℝ in atTop, (2 * n ^ (-(2 / 3 : ℝ))) * R_box ≤ min ρ₁ ρ₂ :=
      (((by simpa using ((ht_eps.const_mul 2).mul_const R_box) :
          Tendsto (fun n : ℝ => (2 * n ^ (-(2 / 3 : ℝ))) * R_box) atTop (𝓝 0))).eventually
        (gt_mem_nhds (lt_min hρ1_pos hρ2_pos))).mono fun _ h => h.le
    have he5 : ∀ᶠ n : ℝ in atTop, C_T1 * √((2 * n ^ (-(2 / 3 : ℝ))) * R_box) ≤ 1 / 2 :=
      (((by simpa using ((((ht_eps.const_mul 2).mul_const R_box).sqrt).const_mul C_T1) :
          Tendsto (fun n : ℝ => C_T1 * √((2 * n ^ (-(2 / 3 : ℝ))) * R_box)) atTop (𝓝 0))).eventually
        (gt_mem_nhds (by norm_num))).mono fun _ h => h.le
    have he6 : ∀ᶠ n : ℝ in atTop, C_T2 * (2 * n ^ (-(2 / 3 : ℝ))) * R_box ^ (5 / 2 : ℝ) ≤ 1 :=
      ((by simpa using (((ht_eps.const_mul 2).const_mul C_T2).mul_const (R_box ^ (5 / 2 : ℝ))) :
          Tendsto (fun n : ℝ => C_T2 * (2 * n ^ (-(2 / 3 : ℝ))) * R_box ^ (5 / 2 : ℝ)) atTop (𝓝 0)).eventually
        (gt_mem_nhds zero_lt_one)).mono fun _ h => h.le
    filter_upwards [eventually_ge_atTop (max 48 (c₄₁ - 1)),
      (ht_N_n.eventually (gt_mem_nhds zero_lt_one)).mono fun _ h => h.le,
      he1, he2,
      (ht_Medge.eventually (gt_mem_nhds zero_lt_one)).mono fun _ h => h.le,
      he3, he4, he5, he6,
      (ht_loga.eventually (gt_mem_nhds zero_lt_one)).mono fun _ h => h.le] with n
        h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    exact ⟨(le_max_left _ _).trans h1, (le_max_right _ _).trans h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hev_n
  let c₀ : ℝ := max 49 (max c₄₁ (N₀ + 1))
  refine ⟨C_RV, c₀, hCRV_pos, (by norm_num : (40 : ℝ) ≤ 49).trans (le_max_left _ _), fun {c} hc => ?_⟩
  intro n a N Φ χ hΦ hM2 hχ_meas hχ_bd hχ_supp
  have hn_N0 : N₀ ≤ n := by dsimp [n]; linarith [le_max_right c₄₁ (N₀ + 1), le_max_right (49 : ℝ) (max c₄₁ (N₀ + 1))]
  obtain ⟨hn48, hc41_n, hNn, hεR_lt, hV_eps, hM_edge, hδ_le, hρ_le, hT1_ub, hT2_ub, hloga_ub⟩ :=
    hN₀ n hn_N0
  have hc49 : 49 ≤ c := (le_max_left _ _).trans hc
  have hc41 : c₄₁ ≤ c := ((le_max_left _ _).trans (le_max_right _ _)).trans hc
  have hn_pos : 0 < n := by linarith
  have hN_pos : 1 ≤ N := Nat.ceil_pos.mpr (Real.log_pos (by linarith))
  have hN_n_bd : 768 * (N : ℝ) ≤ n := (div_le_one hn_pos).mp hNn
  obtain ⟨_, hγ_34, hγ_1, hγ_inv⟩ := spinGamma_pow_bounds hc49 hN_pos hN_n_bd
  set γN := spinGamma a * (spinLambda a ^ (N - 1))⁻¹
  have hγN_pos : 0 < γN := by linarith
  let ε : ℝ := n ^ (-(2 / 3 : ℝ))
  have hε_pos : 0 < ε := Real.rpow_pos_of_pos hn_pos _
  have hεR_γ : ε * (2 * R + 3) < γN / 2 := by linarith
  have hdiff_big : DifferentiableOn ℂ (spinHProfile c N Φ χ) (closedBall (0 : ℂ) (2 * R + 3)) :=
    spinHProfile_differentiableOn hc49 hV (by positivity) hεR_γ hΦ hχ_meas hχ_bd hχ_supp
  refine ⟨hdiff_big.mono (closedBall_subset_closedBall (by linarith)), fun ζ₀ hζ₀ => ?_⟩
  by_cases hH0 : spinHProfile c N Φ χ ζ₀ = 0
  · rw [hH0, norm_zero]; exact hCRV_pos.le
  obtain ⟨_, h41_L1, h41_poly⟩ := h41_all hc41 hΦ hM2
  let c' : ℝ := n * γN
  have hc'_pos : 0 < c' := mul_pos hn_pos hγN_pos
  have hε_tip_le : tipEps c' ≤ 2 * ε := by
    dsimp [ε]; unfold tipEps
    have h1 : (n / 2) ^ (-(2 / 3 : ℝ)) = 2 ^ (2 / 3 : ℝ) * n ^ (-(2 / 3 : ℝ)) := by
      rw [div_eq_mul_inv, Real.mul_rpow (by positivity) (by positivity),
        show (2⁻¹ : ℝ) ^ (-(2 / 3 : ℝ)) = 2 ^ (2 / 3 : ℝ) by rw [← Real.rpow_neg_one, ← Real.rpow_mul (by positivity)]; norm_num]
      ring
    have h2 : (2 : ℝ) ^ (2 / 3 : ℝ) ≤ 2 := Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)
    have hc'_ge : n / 2 ≤ c' := by dsimp [c']; nlinarith
    exact (Real.rpow_le_rpow_of_nonpos (by linarith) hc'_ge (by norm_num)).trans
      (h1.le.trans (by gcongr))
  have htip_eps_ge : ε ≤ tipEps c' := by
    dsimp [ε]; unfold tipEps
    exact Real.rpow_le_rpow_of_nonpos hc'_pos (mul_le_of_le_one_right hn_pos.le hγ_1) (by norm_num)
  let s_N : ℝ := γN ^ (-(1 / 3 : ℝ))
  let δ_shift : ℝ := xiStar * (γN⁻¹ - 1) / tipEps c'
  have hsN_ge1 : 1 ≤ s_N :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hγN_pos hγ_1 (by norm_num)
  have hsN_le2 : s_N ≤ 2 := by
    have hpow : (1 / 2 : ℝ) ^ (-(1 / 3 : ℝ)) = 2 ^ (1 / 3 : ℝ) := by
      rw [one_div, ← Real.rpow_neg_one, ← Real.rpow_mul (by positivity)]; norm_num
    exact (Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)).trans
      (hpow.le.trans (Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)))
  have hδ_nn : 0 ≤ δ_shift := by
    have : 1 ≤ γN⁻¹ := one_le_inv₀ hγN_pos |>.mpr hγ_1
    have := xiStar_pos; have := tipEps_pos hc'_pos
    dsimp [δ_shift]; positivity
  have hδ_le_half : δ_shift ≤ 1 / 2 := by
    dsimp [δ_shift]
    have h1 : xiStar * (γN⁻¹ - 1) ≤ xiStar * (48 * (N : ℝ) / n) := by
      gcongr; exact xiStar_pos.le
    have h2 : n ^ (-(2 / 3 : ℝ)) ≤ tipEps c' := htip_eps_ge
    calc xiStar * (γN⁻¹ - 1) / tipEps c'
        ≤ (xiStar * (48 * (N : ℝ) / n)) / (n ^ (-(2 / 3 : ℝ))) :=
          div_le_div₀ (by positivity [xiStar_pos]) h1 hε_pos h2
      _ = 48 * (N : ℝ) * xiStar / n ^ (1 / 3 : ℝ) := by
          have hr13_pos : 0 < n ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hn_pos _
          rw [Real.rpow_neg hn_pos.le, div_inv_eq_mul, mul_div_assoc', div_mul_eq_mul_div,
            div_eq_div_iff hn_pos.ne' hr13_pos.ne']
          have hadd : n ^ (2 / 3 : ℝ) * n ^ (1 / 3 : ℝ) = n := by
            rw [← Real.rpow_add hn_pos]; norm_num
          calc (xiStar * (48 * (N : ℝ))) * n ^ (2 / 3 : ℝ) * n ^ (1 / 3 : ℝ)
              = (xiStar * (48 * (N : ℝ))) * (n ^ (2 / 3 : ℝ) * n ^ (1 / 3 : ℝ)) := by ring
            _ = (48 * (N : ℝ) * xiStar) * n := by rw [hadd]; ring
      _ ≤ 1 / 2 := hδ_le
  have hrel : ∀ w : ℂ,
      (γN : ℂ) * bScale c' w = (xiStar : ℂ) + (ε : ℂ) * ((w - (δ_shift : ℂ)) / (s_N : ℂ)) := fun w => by
    have hγN_ne : (γN : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hγN_pos.ne'
    have hsN_ne : (s_N : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
    have hγ_tip_s : γN * tipEps c' * s_N = ε := by
      dsimp [c', s_N, ε]; unfold tipEps
      rw [Real.mul_rpow hn_pos.le hγN_pos.le]
      have hgam_p : γN * (γN ^ (-(2 / 3 : ℝ)) * γN ^ (-(1 / 3 : ℝ))) = 1 := by
        nth_rw 1 [← Real.rpow_one γN]
        rw [← Real.rpow_add hγN_pos, ← Real.rpow_add hγN_pos]; norm_num
      calc γN * (n ^ (-(2 / 3 : ℝ)) * γN ^ (-(2 / 3 : ℝ))) * γN ^ (-(1 / 3 : ℝ))
          = n ^ (-(2 / 3 : ℝ)) * (γN * (γN ^ (-(2 / 3 : ℝ)) * γN ^ (-(1 / 3 : ℝ)))) := by ring
        _ = n ^ (-(2 / 3 : ℝ)) := by rw [hgam_p, mul_one]
    have hγ_tip_δ : γN * tipEps c' * δ_shift = xiStar - γN * xiStar := by
      dsimp [δ_shift]
      field_simp [hγN_pos.ne', (tipEps_pos hc'_pos).ne']
    unfold bScale
    calc (γN : ℂ) * ((xiStar : ℂ) + ((tipEps c' : ℝ) : ℂ) * w)
        = (γN : ℂ) * (xiStar : ℂ) + ((γN * tipEps c' : ℝ) : ℂ) * (δ_shift : ℂ) +
            ((γN * tipEps c' * s_N : ℝ) : ℂ) * ((w - (δ_shift : ℂ)) / (s_N : ℂ)) := by
          field_simp [hsN_ne]; push_cast; ring
      _ = (xiStar : ℂ) + (ε : ℂ) * ((w - (δ_shift : ℂ)) / (s_N : ℂ)) := by
          have h1 : (γN : ℂ) * (xiStar : ℂ) + ((γN * tipEps c' : ℝ) : ℂ) * (δ_shift : ℂ) = (xiStar : ℂ) := by
            norm_cast; linarith only [hγ_tip_δ]
          rw [h1, hγ_tip_s]
  let w₀ : ℂ := (δ_shift : ℂ) + (s_N : ℂ) * ζ₀
  let f_sub : ℂ → ℂ := fun w => spinHProfile c N Φ χ ((w - (δ_shift : ℂ)) / (s_N : ℂ))
  have hw₀_norm : ‖w₀‖ ≤ 2 * R + 1 / 2 := by
    have hζ_norm : ‖ζ₀‖ ≤ R := by simpa [dist_zero_right] using mem_closedBall.mp hζ₀
    calc ‖w₀‖ ≤ ‖(δ_shift : ℂ)‖ + ‖(s_N : ℂ) * ζ₀‖ := norm_add_le _ _
      _ = δ_shift + s_N * ‖ζ₀‖ := by
          rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg hδ_nn, abs_of_nonneg (by positivity)]
      _ ≤ 1 / 2 + 2 * R := by gcongr
      _ = 2 * R + 1 / 2 := by ring
  have hf_sub_w₀ : f_sub w₀ = spinHProfile c N Φ χ ζ₀ := by
    dsimp [f_sub, w₀]
    have hsN_ne : (s_N : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
    rw [add_sub_cancel_left, mul_div_cancel_left₀ _ hsN_ne]
  have hf_sub_ne : f_sub w₀ ≠ 0 := by rwa [hf_sub_w₀]
  let r_disc : ℝ := (1 / 2 : ℝ) * (1 + ‖w₀‖) ^ (-(1 / 2 : ℝ))
  have hr_pos : 0 < r_disc := by positivity
  have hr_le_half : r_disc ≤ 1 / 2 := by
    have this : (1 + ‖w₀‖) ^ (-(1 / 2 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith only [norm_nonneg w₀]) (by norm_num)
    dsimp [r_disc]; linarith only [this]
  have hcl_sub : closedBall w₀ r_disc ⊆ ball (0 : ℂ) (2 * R + 2) := by
    intro w hw
    rw [mem_ball, dist_zero_right]
    have h1 := mem_closedBall.mp hw
    rw [dist_eq_norm] at h1
    calc ‖w‖ ≤ ‖w - w₀‖ + ‖w₀‖ := by
          simpa [sub_add_cancel] using norm_add_le (w - w₀) w₀
      _ ≤ r_disc + R_box := add_le_add h1 (by dsimp [R_box]; linarith only [hw₀_norm])
      _ < 2 * R + 2 := by dsimp [R_box]; linarith only [hr_le_half]
  have han_sub : AnalyticOnNhd ℂ f_sub (ball (0 : ℂ) (2 * R + 2)) := by
    have hmap : MapsTo (fun w : ℂ => (w - (δ_shift : ℂ)) / (s_N : ℂ))
        (ball (0 : ℂ) (2 * R + 2)) (ball (0 : ℂ) (2 * R + 3)) := by
      intro w hw
      rw [mem_ball, dist_zero_right] at hw ⊢
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < s_N)]
      calc ‖w - (δ_shift : ℂ)‖ / s_N ≤ (‖w‖ + δ_shift) / 1 := by
            gcongr
            exact (norm_sub_le _ _).trans (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hδ_nn])
        _ < 2 * R + 3 := by rw [div_one]; linarith only [hw, hδ_le_half]
    have han_H : AnalyticOnNhd ℂ (spinHProfile c N Φ χ) (ball (0 : ℂ) (2 * R + 3)) :=
      (hdiff_big.mono ball_subset_closedBall).analyticOnNhd isOpen_ball
    have haff : AnalyticOnNhd ℂ (fun w : ℂ => (w - (δ_shift : ℂ)) / (s_N : ℂ)) univ :=
      ((differentiable_id.sub_const _).div_const _).differentiableOn.analyticOnNhd isOpen_univ
    exact han_H.comp (haff.mono (subset_univ _)) (fun w hw => hmap hw)
  have han_disc : AnalyticOnNhd ℂ f_sub (closedBall w₀ r_disc) := han_sub.mono hcl_sub
  -- Measure zero of zeros + real cut in `ball w₀ r_disc`
  have hbad_null : volume ({w ∈ ball w₀ r_disc | f_sub w = 0} ∪ {w : ℂ | w.im = 0}) = 0 := by
    have hzero_null : volume {w ∈ ball w₀ r_disc | f_sub w = 0} = 0 := by
      classical
      have han_big : AnalyticOnNhd ℂ f_sub (ball w₀ (r_disc + 1 / 4)) :=
        han_sub.mono fun w hw => by
          rw [mem_ball, dist_zero_right]
          rw [mem_ball, dist_eq_norm] at hw
          calc ‖w‖ ≤ ‖w - w₀‖ + ‖w₀‖ := by simpa [sub_add_cancel] using norm_add_le (w - w₀) w₀
            _ < r_disc + 1 / 4 + R_box :=
                add_lt_add_of_lt_of_le hw (by dsimp [R_box]; linarith only [hw₀_norm])
            _ ≤ 2 * R + 2 := by dsimp [R_box]; linarith only [hr_le_half]
      have hnot0 : ¬ EqOn f_sub 0 (ball w₀ (r_disc + 1 / 4)) := fun h =>
        hf_sub_ne (h (mem_ball_self (by positivity)))
      have hev : ∀ z ∈ ball w₀ (r_disc + 1 / 4), ∀ᶠ w in 𝓝[≠] z, f_sub w ≠ 0 := by
        rcases han_big.eqOn_zero_or_eventually_ne_zero_of_preconnected
            (convex_ball w₀ (r_disc + 1 / 4)).isPreconnected with h | h
        · exact absurd h hnot0
        · intro z hz
          filter_upwards [mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp h z hz,
            nhdsWithin_le_nhds (isOpen_ball.mem_nhds hz)] with w hw1 hw2
          rcases hw1 with hw1 | hw1
          · exact hw1
          · exact absurd hw2 hw1
      have hopen : ∀ z ∈ closedBall w₀ r_disc, ∃ δ > 0, ∀ w ∈ ball z δ, w ≠ z → f_sub w ≠ 0 := fun z hz => by
        obtain ⟨U, hU, hUf⟩ := (hev z (closedBall_subset_ball (by linarith only) hz)).exists_mem
        obtain ⟨V', hV', hzV, hVU⟩ := mem_nhdsWithin.mp hU
        obtain ⟨δ, hδ_pos, hδ_sub⟩ := Metric.isOpen_iff.mp hV' z hzV
        exact ⟨δ, hδ_pos, fun w hw hwz => hUf w (hVU ⟨hδ_sub hw, hwz⟩)⟩
      choose δ hδ_pos hδ_ne using hopen
      obtain ⟨s, hs⟩ := (isCompact_closedBall w₀ r_disc).elim_nhds_subcover
        (fun z => if hz : z ∈ closedBall w₀ r_disc then ball z (δ z hz) else ∅)
        fun z hz => by simp only [hz, ↓reduceDIte]; exact ball_mem_nhds z (hδ_pos z hz)
      have hsub : {w ∈ ball w₀ r_disc | f_sub w = 0} ⊆ (s : Set ℂ) := by
        intro w ⟨hw_b, hw0⟩
        obtain ⟨z, hzs, hwz⟩ := mem_iUnion₂.mp (hs.2 (ball_subset_closedBall hw_b))
        have hz_cl := hs.1 z hzs
        simp only [hz_cl, ↓reduceDIte] at hwz
        by_contra hne
        exact absurd hw0 (hδ_ne z hz_cl w hwz fun he => hne (he ▸ hzs))
      exact measure_mono_null hsub (s.finite_toSet.measure_zero volume)
    have hre_null : volume {w : ℂ | w.im = 0} = 0 := by
      let L : Submodule ℝ ℂ := LinearMap.ker Complex.imCLM.toLinearMap
      have hne : L ≠ ⊤ := fun htop => by
        have hI : I ∈ L := htop.symm ▸ Submodule.mem_top
        simp [L, LinearMap.mem_ker] at hI
      have hsub : {w : ℂ | w.im = 0} = (L : Set ℂ) := by ext w; simp [L, LinearMap.mem_ker]
      rw [hsub]; exact MeasureTheory.Measure.addHaar_submodule volume L hne
    exact le_antisymm ((measure_union_le _ _).trans (by rw [hzero_null, hre_null, add_zero])) bot_le
  let B_fn : ℂ → ℝ := fun w => (C_pj + tipH w₀ + 3 * KTip / 4) - Real.log (tipDist w)
  have hB_int : IntegrableOn B_fn (ball w₀ r_disc) := by
    have hc_int : IntegrableOn (fun _ : ℂ => C_pj + tipH w₀ + 3 * KTip / 4) (ball w₀ r_disc) :=
      integrableOn_const (hs := measure_ball_lt_top.ne)
    exact hc_int.add (disc_avg_neg_log_tipDist w₀).1
  have hB_ae : ∀ᵐ w ∂(volume.restrict (ball w₀ r_disc)), Real.log ‖f_sub w‖ ≤ B_fn w := by
    rw [ae_restrict_iff' measurableSet_ball]
    have hcompl := compl_mem_ae_iff.mpr hbad_null
    filter_upwards [hcompl] with w hw_good hw_ball
    have hw_ne0 : f_sub w ≠ 0 := fun h => hw_good (Or.inl ⟨hw_ball, h⟩)
    have hw_cut : ¬ (w.im = 0 ∧ 0 ≤ w.re) := fun h => hw_good (Or.inr h.1)
    have hw_norm : ‖w‖ ≤ R_box := by
      have h1 := mem_ball.mp hw_ball
      rw [dist_eq_norm] at h1
      calc ‖w‖ ≤ ‖w - w₀‖ + ‖w₀‖ := by simpa [sub_add_cancel] using norm_add_le (w - w₀) w₀
        _ ≤ r_disc + (2 * R + 1 / 2) := add_le_add h1.le hw₀_norm
        _ ≤ R_box := by dsimp [R_box]; linarith only [hr_le_half]
    have hεw_pos : 0 ≤ tipEps c' * ‖w‖ := mul_nonneg (tipEps_pos hc'_pos).le (norm_nonneg _)
    have h2ε_nn : 0 ≤ 2 * ε := mul_nonneg zero_le_two hε_pos.le
    have hεw_mul : tipEps c' * ‖w‖ ≤ (2 * ε) * R_box :=
      mul_le_mul hε_tip_le hw_norm (norm_nonneg w) h2ε_nn
    have hεw_ρ₁₂ : tipEps c' * ‖w‖ ≤ min ρ₁ ρ₂ := hεw_mul.trans hρ_le
    have hT1_half : C_T1 * √(tipEps c' * ‖w‖) ≤ 1 / 2 :=
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hεw_mul) hCT1_nn).trans hT1_ub
    have hT2_one : C_T2 * tipEps c' * ‖w‖ ^ (5 / 2 : ℝ) ≤ 1 := by
      have hpow : ‖w‖ ^ (5 / 2 : ℝ) ≤ R_box ^ (5 / 2 : ℝ) :=
        Real.rpow_le_rpow (norm_nonneg w) hw_norm (by norm_num)
      have h1 : C_T2 * tipEps c' ≤ C_T2 * (2 * ε) := mul_le_mul_of_nonneg_left hε_tip_le hCT2_nn
      exact (mul_le_mul h1 hpow (Real.rpow_nonneg (norm_nonneg w) _)
        (mul_nonneg hCT2_nn h2ε_nn)).trans hT2_ub
    have hlog_a : (2 / (0.3 * π)) * ((3 / 2 : ℝ) * √(tipEps c' / slitQ) * √‖w‖) * |Real.log a| ≤ 1 := by
      have heq_a : a = n / 12 := rfl
      rw [heq_a]
      have hsq1 : √(tipEps c' / slitQ) ≤ √(2 * ε / slitQ) :=
        Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hε_tip_le slitQ_pos.le)
      have hsq2 : √‖w‖ ≤ √R_box := Real.sqrt_le_sqrt hw_norm
      have hmid : (3 / 2 : ℝ) * √(tipEps c' / slitQ) * √‖w‖ ≤
          (3 / 2 : ℝ) * √(2 * ε / slitQ) * √R_box :=
        mul_le_mul (mul_le_mul_of_nonneg_left hsq1 (by norm_num)) hsq2 (Real.sqrt_nonneg _)
          (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
      have hleft : (2 / (0.3 * π)) * ((3 / 2 : ℝ) * √(tipEps c' / slitQ) * √‖w‖) ≤
          (2 / (0.3 * π)) * ((3 / 2 : ℝ) * √(2 * ε / slitQ) * √R_box) :=
        mul_le_mul_of_nonneg_left hmid (by positivity)
      exact (mul_le_mul_of_nonneg_right hleft (abs_nonneg _)).trans hloga_ub
    have hq_ne' : spinQSlice c N Φ χ ((γN : ℂ) * bScale c' w) ≠ 0 := by
      intro hq0
      apply hw_ne0
      dsimp only [f_sub, spinHProfile]
      rw [← hrel w, hq0, mul_zero]
    have hpj := spinQSlice_tip_pj_bound hc49 hV hCr_pos hCV_pos hρ1_pos hCT1_nn hρ2_pos hCT2_nn
      hγ_34 hγ_1 hV_eps hM_edge hΦ hχ_meas hχ_bd hχ_supp h41_L1 h41_poly hT1_spec hT2_spec
      hw_cut (hεw_ρ₁₂.trans (min_le_left _ _)) (hεw_ρ₁₂.trans (min_le_right _ _))
      hT1_half hT2_one hlog_a hq_ne'
    have ha_pos : 0 < a := by dsimp [a, n]; linarith only [hc49]
    have hnorm_sub : ‖f_sub w‖ =
        (ε * a) * Real.exp (c' * (tipL (bScale c' w)).re) *
          ‖spinQSlice c N Φ χ ((γN : ℂ) * bScale c' w)‖ := by
      dsimp only [f_sub, spinHProfile]
      rw [← hrel w, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (mul_pos hε_pos ha_pos), Complex.norm_exp]
      congr 2; congr 1
      unfold tipL
      simp only [c', Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, mul_zero, add_zero, sub_zero]
      dsimp [n]
      ring
    have hlog_sub : Real.log ‖f_sub w‖ =
        Real.log (ε * a) + c' * (tipL (bScale c' w)).re +
          Real.log ‖spinQSlice c N Φ χ ((γN : ℂ) * bScale c' w)‖ := by
      rw [hnorm_sub, Real.log_mul (mul_pos (mul_pos hε_pos ha_pos) (Real.exp_pos _)).ne'
        (norm_pos_iff.mpr hq_ne').ne',
        Real.log_mul (mul_pos hε_pos ha_pos).ne' (Real.exp_pos _).ne',
        Real.log_exp]
    have hosc : tipH w ≤ tipH w₀ + 3 * KTip / 4 := by
      have h1 := tipH_disc_oscillation w₀ w hw_ball
      linarith only [(abs_le.mp h1).2]
    dsimp [B_fn]
    linarith only [hpj, hlog_sub, hosc]
  rw [← hf_sub_w₀]
  exact spinS4_4_2_finish hR hw₀_norm han_disc hf_sub_ne hB_ae

/-- info: 'FormalResearch.ModularBootstrap.Spin.spinS4_4_2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spinS4_4_2

end FormalResearch.ModularBootstrap.Spin
