module

public import FormalResearch.ModularBootstrap.Integrality.ReserveCore
public import FormalResearch.ModularBootstrap.Duality.ReserveSeparation

/-!
# Reserve Crossing Measure and Strict–Weak Coincidence (`integrality.tex`, `int:reserve` / `int:strict-weak`)

Completes the lower reserve half of Theorem INT-2 (`int:reserve`) and Corollary INT-2.2
(`int:strict-weak`) in setting `(H_w)` (`prob : FixedWeightProblem`), uniformly for `0 < η ≤ H(c̃)`
with `H(c̃) = o(c̃^{1/3})` (no lower restriction on `η`):

* `cardyRayMeasure`: the terminal-ray Cardy reference measure `ρ_C 1_{[T, ∞)} dt`.
* `int_reserve_ray_ratio_lower`: normalized ray-pairing ratio bound
  `(∫₀^∞ g V) / (∫_T^∞ g V) ≥ (1 - ε) * 2 κ_*^{res} * c̃^{-1/3} η`.
* `int_reserve_measure`, `int_reserve_measure_const`: existence of an admissible crossing measure
  supported on `[T_V(c̃) - η, ∞)` dominating `2 (1 - ε) κ_*^{res} c̃^{-1/3} η ρ_C 1_{[T_V - η, ∞)} dt`.
* `int_strict_weak`: `T_weak(c̃) = T_V(c̃)` for all sufficiently large `c̃`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real ENNReal

namespace FormalResearch.ModularBootstrap.Integrality

open FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Crossing
  FormalResearch.ModularBootstrap.Duality FormalResearch.ModularBootstrap.FixedWeight
  FormalResearch.ModularBootstrap.FixedWeightTip FormalResearch.ModularBootstrap.FixedWeightBand
  FormalResearch.ModularBootstrap.ConcreteBootstrap FormalResearch.ModularBootstrap.Blowup
  FormalResearch.ModularBootstrap.Upper.Rigidity FormalResearch.ModularBootstrap.Stability
  FormalResearch.Special

/-! ### Section 1: Airy profile mass on `(-∞, a₁]` and dominated interval limit -/

private lemma integrable_airyProfile_re :
    Integrable (fun u : ℝ => (airyProfile (u : ℂ)).re) := by
  have h1 : Integrable (fun u : ℝ => airyExtremal (u : ℂ)) :=
    airyExtremalProfile.integrable
  have hre : Integrable (fun u : ℝ => (airyExtremal (u : ℂ)).re) := h1.re
  have heq : (fun u : ℝ => (normProfile airyExtremal (u : ℂ)).re) =
      fun u : ℝ => (profileMass airyExtremal)⁻¹ * (airyExtremal (u : ℂ)).re := by
    ext u; unfold normProfile; simp [Complex.mul_re]
  change Integrable (fun u : ℝ => (normProfile airyExtremal (u : ℂ)).re)
  rw [heq]
  exact hre.const_mul _

private lemma integral_Iic_airyProfile_re :
    ∫ u in Iic (airyZero 1), (airyProfile (u : ℂ)).re = 1 / 2 := by
  have hmass : profileMass airyExtremal = 2 * LStar := by
    change ∫ u : ℝ, ‖airyExtremal (u : ℂ)‖ = 2 * LStar
    exact two_mul_LStar_eq_quantC1Mass.symm
  have hL : ∫ u in Iic (airyZero 1), (airyExtremal (u : ℂ)).re = LStar := by
    have hiC := airyExtremalProfile.integrable
    have hiRe : Integrable (fun u : ℝ => (airyExtremal (u : ℂ)).re) := hiC.re
    have hzero : ∫ u : ℝ, (airyExtremal (u : ℂ)).re = 0 := by
      have h2 : ∫ u : ℝ, (airyExtremal (u : ℂ)).re = (∫ u : ℝ, airyExtremal (u : ℂ)).re :=
        integral_re hiC
      rw [h2, airyExtremal_integral]; rfl
    have hsplit : (∫ u in Iic (airyZero 1), (airyExtremal (u : ℂ)).re) +
        ∫ u in Ioi (airyZero 1), (airyExtremal (u : ℂ)).re =
        ∫ u : ℝ, (airyExtremal (u : ℂ)).re := by
      simpa only [compl_Iic] using integral_add_compl measurableSet_Iic hiRe
    have hIoi_L : -(∫ u in Ioi (airyZero 1), (airyExtremal (u : ℂ)).re) = LStar := by
      rw [← integral_neg]
      refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
      rw [airyExtremal_re, neg_neg]
    rw [hzero] at hsplit
    linarith
  have heq : EqOn (fun u : ℝ => (airyProfile (u : ℂ)).re)
      (fun u : ℝ => (profileMass airyExtremal)⁻¹ * (airyExtremal (u : ℂ)).re) (Iic (airyZero 1)) := by
    intro u _
    unfold airyProfile normProfile
    simp [Complex.mul_re]
  rw [setIntegral_congr_fun measurableSet_Iic heq, integral_const_mul, hL, hmass]
  have hLpos : 0 < LStar := LStar_pos
  field_simp [hLpos.ne']

private lemma tendsto_intervalIntegral_Iic_of_integrable {f : ℝ → ℝ} (hf : Integrable f)
    {a b : ℕ → ℝ} {b₀ : ℝ} (ha : Tendsto a atTop atBot) (hb : Tendsto b atTop (𝓝 b₀)) :
    Tendsto (fun n => ∫ x in a n..b n, f x) atTop (𝓝 (∫ x in Iic b₀, f x)) := by
  have hab : ∀ᶠ n in atTop, a n ≤ b n := by
    filter_upwards [ha.eventually_le_atBot (b₀ - 1),
      hb.eventually (le_mem_nhds (by linarith : b₀ - 1 < b₀))] with n han hbn
    linarith
  have hrew : ∀ᶠ n in atTop, ∫ x in a n..b n, f x = ∫ x : ℝ, (Ioc (a n) (b n)).indicator f x := by
    filter_upwards [hab] with n hle
    rw [intervalIntegral.integral_of_le hle, integral_indicator measurableSet_Ioc]
  rw [← integral_indicator measurableSet_Iic]
  refine Tendsto.congr' (hrew.mono fun _ h => h.symm) ?_
  refine tendsto_integral_of_dominated_convergence (fun x => ‖f x‖)
    (fun n => hf.aestronglyMeasurable.indicator measurableSet_Ioc) hf.norm
    (fun n => Eventually.of_forall fun x => ?_) ?_
  · by_cases hx : x ∈ Ioc (a n) (b n)
    · simp [hx]
    · simp [hx]
  · have hne : ∀ᵐ x : ℝ ∂volume, x ≠ b₀ := by
      rw [ae_iff]
      have : {x : ℝ | ¬x ≠ b₀} = {b₀} := by ext x; simp
      rw [this, Real.volume_singleton]
    filter_upwards [hne] with x hxb
    rcases lt_or_gt_of_ne hxb with hlt | hgt
    · have ha_ev : ∀ᶠ n in atTop, a n < x := ha.eventually_lt_atBot x
      have hb_ev : ∀ᶠ n in atTop, x ≤ b n := hb.eventually (le_mem_nhds hlt)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [ha_ev, hb_ev] with n han hbn
      have h1 : x ∈ Iic b₀ := hlt.le
      have h2 : x ∈ Ioc (a n) (b n) := ⟨han, hbn⟩
      simp [h1, h2]
    · have hb_ev : ∀ᶠ n in atTop, b n < x := hb.eventually (gt_mem_nhds hgt)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hb_ev] with n hbn
      have h1 : x ∉ Iic b₀ := not_le.mpr hgt
      have h2 : x ∉ Ioc (a n) (b n) := fun h => absurd h.2 (not_le.mpr hbn)
      simp [h1, h2]

/-! ### Section 2: Normalized ray integral ratio lower bound (`int:res-bound` ray form) -/

/-- Normalized ray-pairing ratio lower bound (`int:reserve` / `int:hb-reserve`(b) at `m₀ = 1`)
for fixed-weight problems `(H_w)`: for any `ε ∈ (0, 1)` and `H(c̃) = o(c̃^{1/3})`, for all
sufficiently large `c̃`, all `0 < η ≤ H(c̃)`, and all `g ∈ Ā_w` nonnegative on `[T_V(c̃) - η, ∞)`
with `∫_{T_V(c̃)-η}^∞ g V > 0`,
`(∫₀^∞ g V) / (∫_{T_V(c̃)-η}^∞ g V) ≥ (1 - ε) * 2 κ_*^{res} * c̃^{-1/3} η`. -/
theorem int_reserve_ray_ratio_lower (prob : FixedWeightProblem) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1)
    {H : ℝ → ℝ} (hHo : H =o[atTop] fun c : ℝ => c ^ ((1 : ℝ) / 3)) :
    ∃ c₀ : ℝ, max 1 (12 * prob.totalShift) ≤ c₀ ∧
      ∀ {c η : ℝ}, c₀ ≤ c → 0 < η → η ≤ H c →
        ∀ {g : ℝ → ℝ}, TestClass prob (c / 12) g →
          (∀ t : ℝ, prob.T_V c - η ≤ t → 0 ≤ g t) →
          0 < (∫ t in Ici (prob.T_V c - η), g t * prob.cardyV (c / 12) t) →
          (1 - ε) * (2 * kappaRes) * c ^ (-(1 / 3 : ℝ)) * η ≤
            (∫ t in Ioi (0 : ℝ), g t * prob.cardyV (c / 12) t) /
              (∫ t in Ici (prob.T_V c - η), g t * prob.cardyV (c / 12) t) := by
  by_contra h_contra
  push Not at h_contra
  choose c η hc_ge hη_pos hη_le g_raw hg_tc h_nn hray_pos h_viol using fun n : ℕ =>
    h_contra (max (max 1 (12 * prob.totalShift)) ((n : ℝ) + 1)) (le_max_left _ _)
  have hc_tend : Tendsto c atTop atTop := tendsto_atTop_mono
    (fun n => (le_max_right (max 1 (12 * prob.totalShift)) ((n : ℝ) + 1)).trans (hc_ge n))
    (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hc_pos : ∀ n, 0 < c n := fun n =>
    lt_of_lt_of_le zero_lt_one ((le_max_left 1 (12 * prob.totalShift)).trans
      ((le_max_left _ ((n : ℝ) + 1)).trans (hc_ge n)))
  have hshift_n : ∀ n, 12 * prob.totalShift ≤ c n := fun n =>
    (le_max_right 1 (12 * prob.totalShift)).trans ((le_max_left _ ((n : ℝ) + 1)).trans (hc_ge n))
  let B : ℕ → ℝ := fun n => prob.T_V (c n)
  let T : ℕ → ℝ := fun n => B n - η n
  have hη_div_tend : Tendsto (fun n => (c n) ^ (-(1 / 3 : ℝ)) * η n) atTop (𝓝 0) := by
    have hHo_c := hHo.comp_tendsto hc_tend
    have hHo_ratio : Tendsto (fun n => ‖H (c n) / (c n) ^ ((1 : ℝ) / 3)‖) atTop (𝓝 0) := by
      rw [Asymptotics.isLittleO_iff_tendsto' ?_] at hHo_c
      · simpa only [norm_zero, Function.comp_apply] using hHo_c.norm
      · filter_upwards [hc_tend.eventually_gt_atTop 0] with n hcn hzero
        exact absurd hzero (Real.rpow_pos_of_pos hcn _).ne'
    have h_abs_zero : Tendsto (fun n => (c n) ^ (-(1 / 3 : ℝ)) * H (c n)) atTop (𝓝 0) := by
      refine squeeze_zero_norm' ?_ hHo_ratio
      filter_upwards [hc_tend.eventually_gt_atTop 0] with n hcn
      have hp : 0 < (c n) ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hcn _
      rw [Real.norm_eq_abs, abs_mul, Real.rpow_neg hcn.le, abs_of_nonneg (inv_nonneg.mpr hp.le),
        one_div, inv_mul_eq_div, norm_div, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (show 0 < (c n) ^ (3⁻¹ : ℝ) from by simpa only [one_div] using hp)]
    refine squeeze_zero (fun n => mul_nonneg (Real.rpow_nonneg (hc_pos n).le _) (hη_pos n).le)
      (fun n => mul_le_mul_of_nonneg_left (hη_le n) (Real.rpow_nonneg (hc_pos n).le _)) h_abs_zero
  -- Threshold asymptote `S_n → Aopt` and `u_T n → a₁`
  have hS_tend : Tendsto (fun n => (T n - xiBar * c n) / (c n) ^ ((1 : ℝ) / 3)) atTop (𝓝 Aopt) := by
    obtain ⟨c₀B, B₀, _, _, hBbd⟩ := fixedWeight_T_V_sub_TStar_bounded prob
    have h1 : Tendsto (fun n => (B n - TStar (c n)) / (c n) ^ ((1 : ℝ) / 3)) atTop (𝓝 0) := by
      have hB0 : Tendsto (fun n => B₀ * (c n) ^ (-(1 / 3 : ℝ))) atTop (𝓝 0) := by
        simpa only [mul_zero, Function.comp_apply] using
          ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp hc_tend).const_mul B₀
      refine squeeze_zero_norm' ?_ hB0
      filter_upwards [hc_tend.eventually_ge_atTop c₀B, hc_tend.eventually_gt_atTop 0] with n hcn hc0
      have hp : 0 < (c n) ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hc0 _
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hp, div_eq_mul_inv,
        show ((c n) ^ ((1 : ℝ) / 3))⁻¹ = (c n) ^ (-(1 / 3 : ℝ)) by rw [Real.rpow_neg hc0.le, one_div]]
      exact mul_le_mul_of_nonneg_right (hBbd hcn) (Real.rpow_nonneg hc0.le _)
    have h_eq : ∀ᶠ n in atTop, (T n - xiBar * c n) / (c n) ^ ((1 : ℝ) / 3) =
        (B n - TStar (c n)) / (c n) ^ ((1 : ℝ) / 3) + Aopt - (c n) ^ (-(1 / 3 : ℝ)) * η n := by
      filter_upwards [hc_tend.eventually_gt_atTop 0] with n hc0
      have hp : (c n) ^ ((1 : ℝ) / 3) ≠ 0 := (Real.rpow_pos_of_pos hc0 _).ne'
      have hn : (c n) ^ (-(1 / 3 : ℝ)) = ((c n) ^ ((1 : ℝ) / 3))⁻¹ := by
        rw [Real.rpow_neg hc0.le, one_div]
      dsimp [T, B]; unfold TStar
      rw [hn]; field_simp [hp]; ring
    have hlim : Tendsto (fun n =>
        (B n - TStar (c n)) / (c n) ^ ((1 : ℝ) / 3) + Aopt - (c n) ^ (-(1 / 3 : ℝ)) * η n)
        atTop (𝓝 (0 + Aopt - 0)) := (h1.add tendsto_const_nhds).sub hη_div_tend
    simpa only [zero_add, sub_zero] using hlim.congr' (h_eq.mono fun _ h => h.symm)
  -- Eventually `T n ≥ 1 > 0`, so `0 < ∫_{Ici T} g V` implies `g_raw n` is nonzero on `[0, ∞)`
  have hAopt_pos : 0 < Aopt := by
    unfold Aopt
    exact mul_pos cStar_pos (abs_pos.mpr (airyZero_neg 1).ne)
  have hxiBar_pos : 0 < xiBar := by
    unfold xiBar
    exact div_pos (sq_pos_of_pos xiStar_pos) (by norm_num)
  have hT_gt1 : ∀ᶠ n in atTop, 1 ≤ T n := by
    have h1 : ∀ᶠ n in atTop, 1 ≤ xiBar * c n :=
      (hc_tend.const_mul_atTop hxiBar_pos).eventually_ge_atTop 1
    filter_upwards [h1, hc_tend.eventually_gt_atTop 0, hS_tend.eventually (le_mem_nhds hAopt_pos)]
      with n hn hc0 hSn
    have hp : 0 < (c n) ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hc0 _
    have hnum : 0 ≤ T n - xiBar * c n := by
      have := (div_nonneg_iff.mp hSn).resolve_right (fun h => by linarith [h.1])
      exact this.1
    linarith
  -- Lower bound on `∫_{Ioi 0} g_raw V` from `ReserveCore.int_reserve_lower_testClass`
  obtain ⟨c_low, _, h_low⟩ := int_reserve_lower_testClass prob (show (0 : ℝ) < ε / 4 by linarith)
    (show ε / 4 < 1 by linarith) hHo
  have hM_raw_pos : ∀ᶠ n in atTop, 0 < prob.cardyNorm (c n / 12) (g_raw n) := by
    filter_upwards [hT_gt1] with n hTn
    have hnonzero : ∃ t ≥ 0, g_raw n t ≠ 0 := by
      by_contra hall
      push Not at hall
      have h0 : ∫ t in Ici (T n), g_raw n t * prob.cardyV (c n / 12) t = 0 := by
        refine setIntegral_eq_zero_of_forall_eq_zero fun t ht => ?_
        rw [hall t (by linarith [show 1 ≤ T n from hTn, show T n ≤ t from ht]), zero_mul]
      linarith [hray_pos n]
    exact cardyNorm_pos_of_nonzero_general prob (by linarith [hshift_n n]) (hg_tc n) hnonzero
  have hI_raw_lb : ∀ᶠ n in atTop,
      (1 - ε / 4) * kappaRes * (c n) ^ (-(1 / 3 : ℝ)) * η n * prob.cardyNorm (c n / 12) (g_raw n) ≤
        ∫ t in Ioi (0 : ℝ), g_raw n t * prob.cardyV (c n / 12) t := by
    filter_upwards [hc_tend.eventually_ge_atTop c_low, hT_gt1] with n hcn hTn
    have hnonzero : ∃ t ≥ 0, g_raw n t ≠ 0 := by
      by_contra hall
      push Not at hall
      have h0 : ∫ t in Ici (T n), g_raw n t * prob.cardyV (c n / 12) t = 0 := by
        refine setIntegral_eq_zero_of_forall_eq_zero fun t ht => ?_
        rw [hall t (by linarith [show 1 ≤ T n from hTn, show T n ≤ t from ht]), zero_mul]
      linarith [hray_pos n]
    exact h_low hcn (hη_pos n) (hη_le n) (hg_tc n) hnonzero (h_nn n)
  -- Normalize `g n := (M_raw n)⁻¹ • g_raw n`
  let g : ℕ → ℝ → ℝ := fun n t => (prob.cardyNorm (c n / 12) (g_raw n))⁻¹ * g_raw n t
  have hg_tc_norm : ∀ᶠ n in atTop, TestClass prob (c n / 12) (g n) := by
    filter_upwards [hM_raw_pos] with n hMp
    exact (hg_tc n).smul ((prob.cardyNorm (c n / 12) (g_raw n))⁻¹)
  have hg_M : ∀ᶠ n in atTop, prob.cardyNorm (c n / 12) (g n) = 1 := by
    filter_upwards [hM_raw_pos] with n hMp
    unfold FixedWeightProblem.cardyNorm
    have hi_inv : 0 < (prob.cardyNorm (c n / 12) (g_raw n))⁻¹ := inv_pos.mpr hMp
    have heq : (fun t => |g n t| * prob.cardyV (c n / 12) t) =
        fun t => (prob.cardyNorm (c n / 12) (g_raw n))⁻¹ * (|g_raw n t| * prob.cardyV (c n / 12) t) := by
      ext t; dsimp [g]; rw [abs_mul, abs_of_pos hi_inv]; ring
    rw [heq, integral_const_mul]
    exact inv_mul_cancel₀ hMp.ne'
  have hg_nn : ∀ᶠ n in atTop, ∀ t, T n ≤ t → 0 ≤ g n t := by
    filter_upwards [hM_raw_pos] with n hMp t ht
    exact mul_nonneg (inv_nonneg.mpr hMp.le) (h_nn n t ht)
  let I_n : ℕ → ℝ := fun n => ∫ t in Ioi (0 : ℝ), g n t * prob.cardyV (c n / 12) t
  let P_n : ℕ → ℝ := fun n => ∫ t in Ici (T n), g n t * prob.cardyV (c n / 12) t
  have hI_pos : ∀ᶠ n in atTop, 0 < I_n n := by
    filter_upwards [hM_raw_pos, hI_raw_lb] with n hMp hI
    have hVfac : 0 < (1 - ε / 4) * kappaRes * (c n) ^ (-(1 / 3 : ℝ)) * η n *
        prob.cardyNorm (c n / 12) (g_raw n) :=
      mul_pos (mul_pos (mul_pos (mul_pos (by linarith) kappaRes_pos)
        (Real.rpow_pos_of_pos (hc_pos n) _)) (hη_pos n)) hMp
    have hI_raw_pos : 0 < ∫ t in Ioi (0 : ℝ), g_raw n t * prob.cardyV (c n / 12) t :=
      lt_of_lt_of_le hVfac hI
    have heq : I_n n = (prob.cardyNorm (c n / 12) (g_raw n))⁻¹ *
        ∫ t in Ioi (0 : ℝ), g_raw n t * prob.cardyV (c n / 12) t := by
      dsimp [I_n, g]
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => by ring
    rw [heq]
    exact mul_pos (inv_pos.mpr hMp) hI_raw_pos
  have hP_pos : ∀ᶠ n in atTop, 0 < P_n n := by
    filter_upwards [hM_raw_pos] with n hMp
    have heq : P_n n = (prob.cardyNorm (c n / 12) (g_raw n))⁻¹ *
        ∫ t in Ici (T n), g_raw n t * prob.cardyV (c n / 12) t := by
      dsimp [P_n, g]
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ici fun t _ => by ring
    rw [heq]
    exact mul_pos (inv_pos.mpr hMp) (hray_pos n)
  have hP_le_1 : ∀ᶠ n in atTop, P_n n ≤ 1 := by
    filter_upwards [hg_tc_norm, hg_M, hg_nn, hT_gt1] with n hg hM hnn hTn
    have hV_nn : ∀ {t : ℝ}, 0 ≤ t → 0 ≤ prob.cardyV (c n / 12) t := fun {t} ht =>
      prob.cardyV_nonneg (by linarith [hshift_n n]) ht
    have h_eq : P_n n = ∫ t in Ici (T n), |g n t| * prob.cardyV (c n / 12) t :=
      setIntegral_congr_fun measurableSet_Ici fun t ht => by
        rw [abs_of_nonneg (hnn t ht)]
    have h_mono : ∫ t in Ici (T n), |g n t| * prob.cardyV (c n / 12) t ≤
        ∫ t in Ioi (0 : ℝ), |g n t| * prob.cardyV (c n / 12) t :=
      setIntegral_mono_set hg.int_cardy
        (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
            exact mul_nonneg (abs_nonneg _) (hV_nn ht.le))
        (Eventually.of_forall fun t ht => lt_of_lt_of_le (by linarith : (0 : ℝ) < 1) (hTn.trans ht))
    rw [h_eq]; exact h_mono.trans_eq hM
  have hRatio_viol : ∀ᶠ n in atTop,
      I_n n / P_n n < (1 - ε) * (2 * kappaRes) * (c n) ^ (-(1 / 3 : ℝ)) * η n := by
    filter_upwards [hM_raw_pos] with n hMp
    have hIeq : I_n n = (prob.cardyNorm (c n / 12) (g_raw n))⁻¹ *
        ∫ t in Ioi (0 : ℝ), g_raw n t * prob.cardyV (c n / 12) t := by
      dsimp [I_n, g]; rw [← integral_const_mul]
      exact setIntegral_congr_fun measurableSet_Ioi fun t _ => by ring
    have hPeq : P_n n = (prob.cardyNorm (c n / 12) (g_raw n))⁻¹ *
        ∫ t in Ici (T n), g_raw n t * prob.cardyV (c n / 12) t := by
      dsimp [P_n, g]; rw [← integral_const_mul]
      exact setIntegral_congr_fun measurableSet_Ici fun t _ => by ring
    rw [hIeq, hPeq, mul_div_mul_left _ _ (inv_ne_zero hMp.ne')]
    exact h_viol n
  have hI_le_ub : ∀ᶠ n in atTop,
      I_n n < (1 - ε) * (2 * kappaRes) * (c n) ^ (-(1 / 3 : ℝ)) * η n := by
    filter_upwards [hP_pos, hP_le_1, hRatio_viol] with n hPp hP1 hRv
    have h1 := (div_lt_iff₀ hPp).mp hRv
    have h2 : (1 - ε) * (2 * kappaRes) * (c n) ^ (-(1 / 3 : ℝ)) * η n * P_n n ≤
        (1 - ε) * (2 * kappaRes) * (c n) ^ (-(1 / 3 : ℝ)) * η n * 1 := by
      refine mul_le_mul_of_nonneg_left hP1 ?_
      exact mul_nonneg (mul_nonneg (mul_nonneg (by linarith) (mul_pos two_pos kappaRes_pos).le)
        (Real.rpow_nonneg (hc_pos n).le _)) (hη_pos n).le
    linarith
  have hI_tend : Tendsto I_n atTop (𝓝 0) := by
    have hmul : Tendsto (fun n => (1 - ε) * (2 * kappaRes) * (c n) ^ (-(1 / 3 : ℝ)) * η n) atTop (𝓝 0) :=
      ((hη_div_tend.const_mul ((1 - ε) * (2 * kappaRes))).congr fun n => by ring)
        |>.trans (by simp)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmul
      (hI_pos.mono fun _ h => h.le) (hI_le_ub.mono fun _ h => h.le)
  have hsf : ∀ᶠ n in atTop, IsSlackFeasible prob (c n / 12) (T n) (I_n n) (g n) := by
    filter_upwards [hg_tc_norm, hg_M, hg_nn] with n hg hM hnn
    refine ⟨hg, by rw [hM]; exact one_pos, ?_, hnn⟩
    rw [hM, mul_one]
  -- Apply `airy_blnorm_s` + `airy_blnorm` to get `chartUT (c n) (T n) → a₁` and `L¹` convergence
  obtain ⟨D⟩ := proposition_P_of_problem prob
  have hS_hi : ∃ S_hi : ℝ, ∀ᶠ n in atTop, (T n - xiBar * c n) / (c n) ^ ((1 : ℝ) / 3) ≤ S_hi :=
    ⟨Aopt + 1, hS_tend.eventually (ge_mem_nhds (by linarith))⟩
  have hbl_s := airy_blnorm_s D hc_tend hI_tend (hI_pos.mono fun _ h => h.le) hsf hS_hi
  have hAopt_eq : -cStar * airyZero 1 = Aopt := by
    unfold Aopt; rw [abs_of_neg (airyZero_neg 1)]; ring
  have hS_cond : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop,
      (T n - xiBar * c n) / (c n) ^ ((1 : ℝ) / 3) ≤ -cStar * airyZero 1 + δ := fun δ hδ => by
    rw [hAopt_eq]
    exact hS_tend.eventually (ge_mem_nhds (by linarith))
  obtain ⟨-, huT_airy, -, -, -, -, -⟩ := hbl_s.2 hS_cond
  obtain ⟨S_hi, hS_ev⟩ := hS_hi
  obtain ⟨K, hK0, hKev⟩ := sThresh_le_delta_of_eventually hc_tend hS_ev
  have hbl := airy_blnorm D hc_tend hI_tend (hI_pos.mono fun _ h => h.le) hsf ⟨K, hK0, hKev⟩
  have huT_tend : Tendsto (fun n => chartUT (c n) (T n)) atTop (𝓝 (airyZero 1)) := by
    let M_win : ℝ := |airyZero 1| + 1
    obtain ⟨C_ut, c_ut, _, _, hC_ut⟩ := chartUT_sub_uAiry_err (by positivity : 0 ≤ M_win)
    have hdiff : Tendsto (fun n => chartUT (c n) (T n) - uAiry (c n) (T n)) atTop (𝓝 0) := by
      have hut_err : Tendsto (fun n => C_ut * (c n) ^ (-(2 / 3 : ℝ))) atTop (𝓝 0) := by
        simpa using ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp hc_tend).const_mul C_ut
      refine squeeze_zero_norm' ?_ hut_err
      have huT_bd : ∀ᶠ n in atTop, |uAiry (c n) (T n)| ≤ M_win := by
        filter_upwards [Metric.tendsto_nhds.mp huT_airy 1 one_pos] with n hn
        rw [Real.dist_eq] at hn
        exact abs_le.mpr ⟨by linarith [(abs_lt.mp hn).1, neg_abs_le (airyZero 1)],
          by linarith [(abs_lt.mp hn).2, le_abs_self (airyZero 1)]⟩
      filter_upwards [hc_tend.eventually_ge_atTop c_ut, hT_gt1, huT_bd] with n hcn hTn hu
      have h3 := (hC_ut hcn (by linarith) hu).2.2
      rwa [abs_sub_comm] at h3
    simpa using hdiff.add huT_airy
  have huT_cond : ∀ x < airyZero 1, ∀ᶠ n in atTop, x ≤ chartUT (c n) (T n) := fun x hx =>
    huT_tend.eventually (le_mem_nhds hx)
  obtain ⟨-, -, hl1_tend, -⟩ := hbl.2 huT_cond
  -- Now prove `P_n → 1/2` via `L¹` convergence on `[-A_n², A_n²]`
  obtain ⟨c_S, _, _, _, hcS, _, _, _, key⟩ := densityHyp_of_slack D
  have hI4 : ∀ᶠ n in atTop, I_n n ≤ 1 / 4 := hI_tend.eventually (ge_mem_nhds (by norm_num))
  have hA2_tend : Tendsto (fun n => chartAC D.r_1 (c n) ^ 2) atTop atTop :=
    (tendsto_chartAC_sq D.hr1_pos).comp hc_tend
  have hA2_neg_tend : Tendsto (fun n => -(chartAC D.r_1 (c n) ^ 2)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp hA2_tend
  have huT_in : ∀ᶠ n in atTop,
      chartUT (c n) (T n) ∈ Icc (-(chartAC D.r_1 (c n) ^ 2)) (chartAC D.r_1 (c n) ^ 2) := by
    filter_upwards [hA2_tend.eventually_gt_atTop (|airyZero 1| + 1),
      huT_tend.eventually (Metric.ball_mem_nhds (airyZero 1) one_pos)] with n hA hn
    rw [Real.dist_eq] at hn
    refine ⟨?_, ?_⟩
    · linarith [(abs_lt.mp hn).1, neg_abs_le (airyZero 1)]
    · linarith [(abs_lt.mp hn).2, le_abs_self (airyZero 1)]
  have hF_int_ev : ∀ᶠ n in atTop, Integrable ((Icc (-(chartAC D.r_1 (c n) ^ 2))
      (chartAC D.r_1 (c n) ^ 2)).indicator (fun x : ℝ => psiTilde prob (c n) (g n) (x : ℂ))) := by
    filter_upwards [hc_tend.eventually_ge_atTop c_S, hI_pos, hI4, hsf, hKev,
      hA2_tend.eventually_gt_atTop K] with n hcS_n hIp hI4_n hsf_n hK_n hKA
    have hc'_pos : 0 < c n := D.hc₀_pos.trans_le (hcS.trans hcS_n)
    have hint : T n < virasoroDeltaChart (c n) (-(chartAC D.r_1 (c n) ^ 2)) :=
      interior_of_le_neg D.hr1_pos hc'_pos hK0 hKA hK_n
    obtain ⟨_, hdens, _, _⟩ := key hcS_n hIp.le hI4_n hsf_n hint
    rw [integrable_indicator_iff measurableSet_Icc]
    exact (hdens.analytic.continuousOn.comp Complex.continuous_ofReal.continuousOn
      fun x hx => DensityHyp.mem_ball_of_real hx).integrableOn_Icc
  have hAiry_int : Integrable (fun x : ℝ => airyProfile (x : ℂ)) := by
    unfold airyProfile normProfile
    exact airyExtremalProfile.integrable.const_mul _
  -- Piece 1: `∫_{-A_n²}^{u_T n} Re Ψ_n → 1/2`
  have h_piece1_tend : Tendsto (fun n =>
      ∫ u in (-(chartAC D.r_1 (c n) ^ 2))..(chartUT (c n) (T n)),
        (psiTilde prob (c n) (g n) (u : ℂ)).re) atTop (𝓝 (1 / 2 : ℝ)) := by
    have h_air_tend := tendsto_intervalIntegral_Iic_of_integrable integrable_airyProfile_re
      hA2_neg_tend huT_tend
    rw [integral_Iic_airyProfile_re] at h_air_tend
    have hdiff_tend : Tendsto (fun n =>
        (∫ u in (-(chartAC D.r_1 (c n) ^ 2))..(chartUT (c n) (T n)),
          (psiTilde prob (c n) (g n) (u : ℂ)).re) -
        (∫ u in (-(chartAC D.r_1 (c n) ^ 2))..(chartUT (c n) (T n)),
          (airyProfile (u : ℂ)).re)) atTop (𝓝 0) := by
      refine squeeze_zero_norm' ?_ hl1_tend
      filter_upwards [huT_in, hF_int_ev] with n hu hF_int
      let A2 : ℝ := chartAC D.r_1 (c n) ^ 2
      let uT_n : ℝ := chartUT (c n) (T n)
      let F : ℝ → ℂ := (Icc (-A2) A2).indicator (fun x : ℝ => psiTilde prob (c n) (g n) (x : ℂ))
      have hF_re_eq : ∫ u in (-A2)..uT_n, (psiTilde prob (c n) (g n) (u : ℂ)).re =
          ∫ u in Ioc (-A2) uT_n, (F u).re := by
        rw [intervalIntegral.integral_of_le hu.1]
        refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
        have hxIcc : x ∈ Icc (-A2) A2 := ⟨hx.1.le, hx.2.trans hu.2⟩
        simp [F, hxIcc]
      have hAiry_re_eq : ∫ u in (-A2)..uT_n, (airyProfile (u : ℂ)).re =
          ∫ u in Ioc (-A2) uT_n, (airyProfile (u : ℂ)).re :=
        intervalIntegral.integral_of_le hu.1
      have hF_re : Integrable (fun u : ℝ => (F u).re) := hF_int.re
      have hAiry_re : Integrable (fun u : ℝ => (airyProfile (u : ℂ)).re) := hAiry_int.re
      rw [hF_re_eq, hAiry_re_eq, ← integral_sub hF_re.integrableOn hAiry_re.integrableOn]
      calc ‖∫ u in Ioc (-A2) uT_n, ((F u).re - (airyProfile (u : ℂ)).re)‖
          ≤ ∫ u in Ioc (-A2) uT_n, ‖(F u).re - (airyProfile (u : ℂ)).re‖ := norm_integral_le_integral_norm _
        _ ≤ ∫ u : ℝ, ‖(F u).re - (airyProfile (u : ℂ)).re‖ :=
            setIntegral_le_integral (hF_re.sub hAiry_re).norm
              (Eventually.of_forall fun u => norm_nonneg _)
        _ ≤ ∫ u : ℝ, ‖F u - airyProfile (u : ℂ)‖ := by
            refine integral_mono (hF_re.sub hAiry_re).norm (hF_int.sub hAiry_int).norm fun u => ?_
            rw [← Complex.sub_re, Real.norm_eq_abs]
            exact Complex.abs_re_le_norm _
    simpa only [zero_add, sub_add_cancel] using hdiff_tend.add h_air_tend
  -- Piece 2 & combined `P_n → 1/2`
  have h_l1_norm_tend : Tendsto (fun n => ∫ x : ℝ,
      ‖(Icc (-(chartAC D.r_1 (c n) ^ 2)) (chartAC D.r_1 (c n) ^ 2)).indicator
        (fun x : ℝ => psiTilde prob (c n) (g n) (x : ℂ)) x‖) atTop (𝓝 1) := by
    have h_airy_norm : ∫ x : ℝ, ‖airyProfile (x : ℂ)‖ = 1 :=
      normProfile_integral_norm airyExtremalProfile
    have h_norm_diff : Tendsto (fun n => (∫ x : ℝ,
        ‖(Icc (-(chartAC D.r_1 (c n) ^ 2)) (chartAC D.r_1 (c n) ^ 2)).indicator
          (fun x : ℝ => psiTilde prob (c n) (g n) (x : ℂ)) x‖) -
        ∫ x : ℝ, ‖airyProfile (x : ℂ)‖) atTop (𝓝 0) := by
      refine squeeze_zero_norm' ?_ hl1_tend
      filter_upwards [hF_int_ev] with n hF_int
      let F := (Icc (-(chartAC D.r_1 (c n) ^ 2)) (chartAC D.r_1 (c n) ^ 2)).indicator
        (fun x : ℝ => psiTilde prob (c n) (g n) (x : ℂ))
      rw [Real.norm_eq_abs, ← integral_sub hF_int.norm hAiry_int.norm]
      calc |∫ x : ℝ, (‖F x‖ - ‖airyProfile (x : ℂ)‖)|
          ≤ ∫ x : ℝ, |‖F x‖ - ‖airyProfile (x : ℂ)‖| := abs_integral_le_integral_abs
        _ ≤ ∫ x : ℝ, ‖F x - airyProfile (x : ℂ)‖ :=
            integral_mono (hF_int.norm.sub hAiry_int.norm).abs (hF_int.sub hAiry_int).norm
              fun x => abs_norm_sub_norm_le _ _
    rw [← h_airy_norm]
    simpa only [zero_add, sub_add_cancel] using h_norm_diff.add_const (∫ x : ℝ, ‖airyProfile (x : ℂ)‖)
  have h_P_eq_and_tail : ∀ᶠ n in atTop,
      P_n n = (∫ u in (-(chartAC D.r_1 (c n) ^ 2))..(chartUT (c n) (T n)),
          (psiTilde prob (c n) (g n) (u : ℂ)).re) +
        ∫ t in Ioi (virasoroDeltaChart (c n) (-(chartAC D.r_1 (c n) ^ 2))),
          g n t * prob.cardyV (c n / 12) t ∧
      0 ≤ ∫ t in Ioi (virasoroDeltaChart (c n) (-(chartAC D.r_1 (c n) ^ 2))),
          g n t * prob.cardyV (c n / 12) t ∧
      ∫ t in Ioi (virasoroDeltaChart (c n) (-(chartAC D.r_1 (c n) ^ 2))),
          g n t * prob.cardyV (c n / 12) t ≤
        1 - ∫ x : ℝ, ‖(Icc (-(chartAC D.r_1 (c n) ^ 2)) (chartAC D.r_1 (c n) ^ 2)).indicator
          (fun x : ℝ => psiTilde prob (c n) (g n) (x : ℂ)) x‖ := by
    filter_upwards [hc_tend.eventually_ge_atTop c_S, hI_pos, hI4, hsf, hKev,
      hA2_tend.eventually_gt_atTop K, hT_gt1, hg_tc_norm, hg_M, hg_nn] with
        n hcS_n hIp hI4_n hsf_n hK_n hKA hTn hgn hMn hnn_g
    have hc'_pos : 0 < c n := D.hc₀_pos.trans_le (hcS.trans hcS_n)
    have hV_nn : ∀ {t : ℝ}, 0 ≤ t → 0 ≤ prob.cardyV (c n / 12) t := fun ht =>
      prob.cardyV_nonneg (by linarith [hshift_n n]) ht
    have hint : T n < virasoroDeltaChart (c n) (-(chartAC D.r_1 (c n) ^ 2)) :=
      interior_of_le_neg D.hr1_pos hc'_pos hK0 hKA hK_n
    obtain ⟨_, _, hT_lo, _⟩ := key hcS_n hIp.le hI4_n hsf_n hint
    let A2 : ℝ := chartAC D.r_1 (c n) ^ 2
    let t_lo : ℝ := virasoroDeltaChart (c n) A2
    let t_hi : ℝ := virasoroDeltaChart (c n) (-A2)
    have hA2_vir := chartAC_sq_le_virasoroAC_sq D.hr1_pos hc'_pos.le
    obtain ⟨huT_mem, huT_eq⟩ := chartUT_mem_Icc_of_between' D.hr1_pos hc'_pos hT_lo.le hint.le
    have hgv_int : IntegrableOn (fun t => g n t * prob.cardyV (c n / 12) t) (Ioi 0) :=
      hgn.int_cardy.norm.mono'
        (((hgn.cont.mul (continuous_cardyV prob (c n / 12)).continuousOn).mono
          Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi)
        (Eventually.of_forall fun t => by simp [Real.norm_eq_abs])
    have hT_hi_le : T n ≤ t_hi := hint.le
    have hT_nn : 0 ≤ T n := by linarith
    have ht_lo_nn : 0 ≤ t_lo :=
      (virasoroDeltaChart_pos hc'_pos (chart_real_abs_le_virasoro D.hr1_pos hc'_pos
        (by rw [abs_of_nonneg (sq_nonneg _)]))).le
    have ht_lo_hi : t_lo ≤ t_hi := (hT_lo.trans hint).le
    have hre_T : ∫ u in (-A2)..(chartUT (c n) (T n)),
        (psiTilde prob (c n) (g n) (u : ℂ)).re =
        ∫ t in (T n)..t_hi, g n t * prob.cardyV (c n / 12) t := by
      have hre := psiTilde_re_integral_eq prob hc'_pos hgn
        (by linarith [hA2_vir]) (huT_mem.2.trans hA2_vir) huT_mem.1
      rw [hre, huT_eq, hMn, inv_one, one_mul]
    have hP_split : P_n n = (∫ t in (T n)..t_hi, g n t * prob.cardyV (c n / 12) t) +
        ∫ t in Ioi t_hi, g n t * prob.cardyV (c n / 12) t := by
      dsimp [P_n]
      rw [setIntegral_congr_set Ioi_ae_eq_Ici.symm]
      rw [intervalIntegral.integral_of_le hT_hi_le, ← setIntegral_union Ioc_disjoint_Ioi_same
        measurableSet_Ioi (hgv_int.mono_set fun _ hx => hT_nn.trans_lt hx.1)
        (hgv_int.mono_set (Ioi_subset_Ioi (hT_nn.trans hT_hi_le))), Ioc_union_Ioi_eq_Ioi hT_hi_le]
    have htail_nn : 0 ≤ ∫ t in Ioi t_hi, g n t * prob.cardyV (c n / 12) t :=
      setIntegral_nonneg measurableSet_Ioi fun t ht =>
        mul_nonneg (hnn_g t (hT_hi_le.trans (mem_Ioi.mp ht).le))
          (hV_nn (hT_nn.trans (hT_hi_le.trans (mem_Ioi.mp ht).le)))
    have htail_eq_abs : ∫ t in Ioi t_hi, g n t * prob.cardyV (c n / 12) t =
        ∫ t in Ioi t_hi, |g n t| * prob.cardyV (c n / 12) t :=
      setIntegral_congr_fun measurableSet_Ioi fun t ht => by
        rw [abs_of_nonneg (hnn_g t (hT_hi_le.trans (mem_Ioi.mp ht).le))]
    have hnorm_mid : ∫ x : ℝ, ‖(Icc (-A2) A2).indicator
          (fun x : ℝ => psiTilde prob (c n) (g n) (x : ℂ)) x‖ =
        ∫ t in t_lo..t_hi, |g n t| * prob.cardyV (c n / 12) t := by
      have h_eq_ind : ∫ x : ℝ, ‖(Icc (-A2) A2).indicator
            (fun x : ℝ => psiTilde prob (c n) (g n) (x : ℂ)) x‖ =
          ∫ x in (-A2)..A2, ‖psiTilde prob (c n) (g n) (x : ℂ)‖ := by
        have h1 : (fun x : ℝ => ‖(Icc (-A2) A2).indicator
              (fun y : ℝ => psiTilde prob (c n) (g n) (y : ℂ)) x‖) =
            (Icc (-A2) A2).indicator (fun x : ℝ => ‖psiTilde prob (c n) (g n) (x : ℂ)‖) := by
          ext x
          by_cases hx : x ∈ Icc (-A2) A2 <;> simp [hx]
        rw [h1, integral_indicator measurableSet_Icc,
          intervalIntegral.integral_of_le (by linarith [sq_nonneg (chartAC D.r_1 (c n))]),
          setIntegral_congr_set Ioc_ae_eq_Icc]
      rw [h_eq_ind, psiTilde_norm_integral_eq prob hc'_pos hV_nn hgn (by rw [hMn]; exact zero_lt_one)
        (by linarith [hA2_vir]) hA2_vir (by linarith [sq_nonneg (chartAC D.r_1 (c n))]),
        hMn, inv_one, one_mul]
    have htail_le : ∫ t in Ioi t_hi, g n t * prob.cardyV (c n / 12) t ≤
        1 - ∫ x : ℝ, ‖(Icc (-A2) A2).indicator
          (fun x : ℝ => psiTilde prob (c n) (g n) (x : ℂ)) x‖ := by
      rw [hnorm_mid, htail_eq_abs]
      have htot_split : prob.cardyNorm (c n / 12) (g n) =
          (∫ t in (0 : ℝ)..t_hi, |g n t| * prob.cardyV (c n / 12) t) +
            ∫ t in Ioi t_hi, |g n t| * prob.cardyV (c n / 12) t := by
        unfold FixedWeightProblem.cardyNorm
        rw [intervalIntegral.integral_of_le (ht_lo_nn.trans ht_lo_hi),
          ← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
            (hgn.int_cardy.mono_set Ioc_subset_Ioi_self)
            (hgn.int_cardy.mono_set (Ioi_subset_Ioi (ht_lo_nn.trans ht_lo_hi))),
          Ioc_union_Ioi_eq_Ioi (ht_lo_nn.trans ht_lo_hi)]
      have h0_hi : ∫ t in (0 : ℝ)..t_hi, |g n t| * prob.cardyV (c n / 12) t =
          (∫ t in (0 : ℝ)..t_lo, |g n t| * prob.cardyV (c n / 12) t) +
            ∫ t in t_lo..t_hi, |g n t| * prob.cardyV (c n / 12) t := by
        have hcont : ContinuousOn (fun t => |g n t| * prob.cardyV (c n / 12) t) (Ici 0) :=
          hgn.cont.abs.mul (continuous_cardyV prob (c n / 12)).continuousOn
        exact (intervalIntegral.integral_add_adjacent_intervals
          ((hcont.mono Icc_subset_Ici_self).intervalIntegrable_of_Icc ht_lo_nn)
          ((hcont.mono fun t (ht : t ∈ Set.Icc t_lo t_hi) => ht_lo_nn.trans ht.1).intervalIntegrable_of_Icc
            ht_lo_hi)).symm
      have h0_lo_nn : 0 ≤ ∫ t in (0 : ℝ)..t_lo, |g n t| * prob.cardyV (c n / 12) t := by
        rw [intervalIntegral.integral_of_le ht_lo_nn]
        exact setIntegral_nonneg measurableSet_Ioc fun t ht =>
          mul_nonneg (abs_nonneg _) (hV_nn ht.1.le)
      linarith [hMn]
    exact ⟨by rw [hP_split, hre_T], htail_nn, htail_le⟩
  have h_tail_tend : Tendsto (fun n =>
      ∫ t in Ioi (virasoroDeltaChart (c n) (-(chartAC D.r_1 (c n) ^ 2))),
        g n t * prob.cardyV (c n / 12) t) atTop (𝓝 0) := by
    have h_ub : Tendsto (fun n => 1 - ∫ x : ℝ, ‖(Icc (-(chartAC D.r_1 (c n) ^ 2))
        (chartAC D.r_1 (c n) ^ 2)).indicator
          (fun x : ℝ => psiTilde prob (c n) (g n) (x : ℂ)) x‖) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h_l1_norm_tend
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_ub
      (h_P_eq_and_tail.mono fun _ h => h.2.1) (h_P_eq_and_tail.mono fun _ h => h.2.2)
  have h_P_tend : Tendsto P_n atTop (𝓝 (1 / 2 : ℝ)) := by
    have hsum : Tendsto (fun n =>
        (∫ u in (-(chartAC D.r_1 (c n) ^ 2))..(chartUT (c n) (T n)),
          (psiTilde prob (c n) (g n) (u : ℂ)).re) +
        ∫ t in Ioi (virasoroDeltaChart (c n) (-(chartAC D.r_1 (c n) ^ 2))),
          g n t * prob.cardyV (c n / 12) t) atTop (𝓝 (1 / 2 + 0)) :=
      h_piece1_tend.add h_tail_tend
    rw [add_zero] at hsum
    exact hsum.congr' (h_P_eq_and_tail.mono fun _ h => h.1.symm)
  -- Final contradiction: `(1 - ε/4)/(1/2 + δ) > (1 - ε)*2` for small `δ`, violating `hRatio_viol`
  have h_ratio_close : ∃ δ > 0, (1 - ε) * 2 < (1 - ε / 4) / (1 / 2 + δ) := by
    have hlt : (1 - ε) * 2 < (1 - ε / 4) / (1 / 2) := by linarith
    have hcont : ContinuousAt (fun d : ℝ => (1 - ε / 4) / (1 / 2 + d)) 0 := by
      refine ContinuousAt.div continuousAt_const (continuousAt_const.add continuousAt_id) ?_
      norm_num
    obtain ⟨r, hr_pos, hr⟩ := Metric.continuousAt_iff.mp hcont ((1 - ε / 4) / (1 / 2) - (1 - ε) * 2)
      (by linarith)
    refine ⟨r / 2, half_pos hr_pos, ?_⟩
    have h1 := hr (by rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hr_pos)]; linarith)
    rw [Real.dist_eq, add_zero] at h1
    linarith [(abs_lt.mp h1).1]
  obtain ⟨δ, hδ_pos, hδ_lt⟩ := h_ratio_close
  have h_final_ev : ∀ᶠ n in atTop,
      I_n n ≥ (1 - ε / 4) * kappaRes * (c n) ^ (-(1 / 3 : ℝ)) * η n ∧
      P_n n ≤ 1 / 2 + δ ∧ 0 < P_n n ∧
      I_n n / P_n n < (1 - ε) * (2 * kappaRes) * (c n) ^ (-(1 / 3 : ℝ)) * η n := by
    filter_upwards [hM_raw_pos, hI_raw_lb,
      h_P_tend.eventually (ge_mem_nhds (show (1 / 2 : ℝ) < 1 / 2 + δ by linarith)),
      hP_pos, hRatio_viol] with n hMp hI hP_ub hPp hRv
    refine ⟨?_, hP_ub, hPp, hRv⟩
    have hIeq : I_n n = (prob.cardyNorm (c n / 12) (g_raw n))⁻¹ *
        ∫ t in Ioi (0 : ℝ), g_raw n t * prob.cardyV (c n / 12) t := by
      dsimp [I_n, g]; rw [← integral_const_mul]
      exact setIntegral_congr_fun measurableSet_Ioi fun t _ => by ring
    rw [hIeq]
    have hmul := mul_le_mul_of_nonneg_left hI (inv_nonneg.mpr hMp.le)
    have hid : (prob.cardyNorm (c n / 12) (g_raw n))⁻¹ *
        ((1 - ε / 4) * kappaRes * (c n) ^ (-(1 / 3 : ℝ)) * η n *
          prob.cardyNorm (c n / 12) (g_raw n)) =
        (1 - ε / 4) * kappaRes * (c n) ^ (-(1 / 3 : ℝ)) * η n := by
      field_simp [hMp.ne']
    linarith
  obtain ⟨n, hI_lb, hP_ub, hP_pos_n, hRv_n⟩ := h_final_ev.exists
  have h_num_nn : 0 ≤ (1 - ε / 4) * kappaRes * (c n) ^ (-(1 / 3 : ℝ)) * η n :=
    mul_nonneg (mul_nonneg (mul_nonneg (by linarith) kappaRes_pos.le)
      (Real.rpow_nonneg (hc_pos n).le _)) (hη_pos n).le
  have h1 : (1 - ε / 4) * kappaRes * (c n) ^ (-(1 / 3 : ℝ)) * η n / (1 / 2 + δ) ≤ I_n n / P_n n :=
    div_le_div₀ (by linarith [hI_lb]) hI_lb hP_pos_n hP_ub
  have hfac_pos : 0 < kappaRes * (c n) ^ (-(1 / 3 : ℝ)) * η n :=
    mul_pos (mul_pos kappaRes_pos (Real.rpow_pos_of_pos (hc_pos n) _)) (hη_pos n)
  have hlt2 : (1 - ε) * (2 * kappaRes) * (c n) ^ (-(1 / 3 : ℝ)) * η n <
      (1 - ε / 4) * kappaRes * (c n) ^ (-(1 / 3 : ℝ)) * η n / (1 / 2 + δ) := by
    have heq1 : (1 - ε) * (2 * kappaRes) * (c n) ^ (-(1 / 3 : ℝ)) * η n =
        ((1 - ε) * 2) * (kappaRes * (c n) ^ (-(1 / 3 : ℝ)) * η n) := by ring
    have heq2 : (1 - ε / 4) * kappaRes * (c n) ^ (-(1 / 3 : ℝ)) * η n / (1 / 2 + δ) =
        ((1 - ε / 4) / (1 / 2 + δ)) * (kappaRes * (c n) ^ (-(1 / 3 : ℝ)) * η n) := by ring
    rw [heq1, heq2]
    exact mul_lt_mul_of_pos_right hδ_lt hfac_pos
  linarith

/-! ### Section 3: Reserve crossing measure (`int:res-meas`) and strict–weak equality (`int:strict-weak`) -/

/-- Terminal-ray Cardy reference measure `ρ_C(t) 1_{[T, ∞)}(t) dt`, with `ρ_C(t) = 2π V(t)`. -/
noncomputable def cardyRayMeasure (prob : FixedWeightProblem) (c T : ℝ) : Measure ℝ :=
  (volume.withDensity fun t => ENNReal.ofReal (prob.cardyDensity (c / 12) t)).restrict (Ici T)

lemma isFiniteMeasureOnCompacts_cardyRayMeasure (prob : FixedWeightProblem) (c T : ℝ) :
    IsFiniteMeasureOnCompacts (cardyRayMeasure prob c T) := by
  refine ⟨fun K hK => ?_⟩
  unfold cardyRayMeasure
  have hcont : Continuous fun t => prob.cardyDensity (c / 12) t := by
    unfold FixedWeightProblem.cardyDensity
    exact continuous_const.mul (continuous_cardyV prob (c / 12))
  have hmeas : Measurable fun t => ENNReal.ofReal (prob.cardyDensity (c / 12) t) :=
    ENNReal.continuous_ofReal.measurable.comp hcont.measurable
  rw [Measure.restrict_apply hK.measurableSet,
    withDensity_apply _ (hK.measurableSet.inter measurableSet_Ici)]
  rcases eq_empty_or_nonempty K with rfl | hKne
  · simp
  · obtain ⟨B, hB⟩ := (hK.image hcont).bddAbove
    have hle : ∫⁻ t in K ∩ Ici T, ENNReal.ofReal (prob.cardyDensity (c / 12) t) ∂volume ≤
        ENNReal.ofReal B * volume K := by
      calc ∫⁻ t in K ∩ Ici T, ENNReal.ofReal (prob.cardyDensity (c / 12) t) ∂volume
          = ∫⁻ t : ℝ, (K ∩ Ici T).indicator
              (fun s => ENNReal.ofReal (prob.cardyDensity (c / 12) s)) t :=
              (lintegral_indicator (hK.measurableSet.inter measurableSet_Ici) _).symm
        _ ≤ ∫⁻ t : ℝ, K.indicator (fun _ => ENNReal.ofReal B) t := by
              refine lintegral_mono fun t => ?_
              by_cases ht : t ∈ K ∩ Ici T
              · simp [ht, ht.1, ENNReal.ofReal_le_ofReal (hB ⟨t, ht.1, rfl⟩)]
              · simp [ht]
        _ = ENNReal.ofReal B * volume K := by
              rw [lintegral_indicator hK.measurableSet, setLIntegral_const]
    exact lt_of_le_of_lt hle (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.measure_lt_top)

/-- Reserve crossing measure (`int:res-meas`, `int:hb-reserve`(b) at `m₀ = 1`) for fixed-weight
problems `(H_w)`: uniformly for `0 < η ≤ H(c̃)` with `H(c̃) = o(c̃^{1/3})`, there exists an
admissible crossing measure supported on `[T_V(c̃) - η, ∞)` dominating
`2 (1 - ε) κ_*^{res} c̃^{-1/3} η · ρ_C 1_{[T_V(c̃) - η, ∞)} dt`. -/
theorem int_reserve_measure (prob : FixedWeightProblem) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1)
    {H : ℝ → ℝ} (hHo : H =o[atTop] fun c : ℝ => c ^ ((1 : ℝ) / 3)) :
    ∃ c₀ : ℝ, max 1 (12 * prob.totalShift) ≤ c₀ ∧
      ∀ {c η : ℝ}, c₀ ≤ c → 0 < η → η ≤ H c →
        ∃ meas : AdmissibleCrossingMeasure prob (c / 12),
          meas.ν (Ici (prob.T_V c - η))ᶜ = 0 ∧
          ENNReal.ofReal (2 * (1 - ε) * kappaRes * c ^ (-(1 / 3 : ℝ)) * η) •
            cardyRayMeasure prob c (prob.T_V c - η) ≤ meas.ν := by
  obtain ⟨c_ratio, hc_ratio, h_ratio⟩ := int_reserve_ray_ratio_lower prob hε0 hε1 hHo
  obtain ⟨β₀, hβ₀_pos, hβ₀_half, ht0⟩ := exists_beta0 prob.w zero_lt_one
  have hT_ge1 : ∀ᶠ c in atTop, 1 ≤ prob.T_V c - max 0 (H c) := by
    obtain ⟨c₀B, B₀, _, _, hBbd⟩ := fixedWeight_T_V_sub_TStar_bounded prob
    have hHo_c : Tendsto (fun c => c ^ (-(1 / 3 : ℝ)) * max 0 (H c)) atTop (𝓝 0) := by
      have hHo_r : Tendsto (fun c : ℝ => ‖H c / c ^ ((1 : ℝ) / 3)‖) atTop (𝓝 0) := by
        rw [Asymptotics.isLittleO_iff_tendsto' ?_] at hHo
        · simpa using hHo.norm
        · filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc h0
          exact absurd h0 (Real.rpow_pos_of_pos hc _).ne'
      refine squeeze_zero_norm' ?_ hHo_r
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
      have hp : 0 < c ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hc _
      rw [Real.norm_eq_abs, abs_mul, Real.rpow_neg hc.le, abs_of_nonneg (inv_nonneg.mpr hp.le),
        one_div, inv_mul_eq_div, norm_div, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (show 0 < c ^ (3⁻¹ : ℝ) from by simpa only [one_div] using hp)]
      rcases le_total 0 (H c) with h | h
      · rw [max_eq_right h]
      · rw [max_eq_left h, abs_zero, zero_div]
        exact div_nonneg (abs_nonneg _) (Real.rpow_nonneg hc.le _)
    have hB_tend : Tendsto (fun c => (prob.T_V c - xiBar * c) / c ^ ((1 : ℝ) / 3)) atTop (𝓝 Aopt) := by
      have h1 : Tendsto (fun c => (prob.T_V c - TStar c) / c ^ ((1 : ℝ) / 3)) atTop (𝓝 0) := by
        have hB0 : Tendsto (fun c => B₀ * c ^ (-(1 / 3 : ℝ))) atTop (𝓝 0) := by
          simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).const_mul B₀
        refine squeeze_zero_norm' ?_ hB0
        filter_upwards [eventually_ge_atTop c₀B, eventually_gt_atTop (0 : ℝ)] with c hcn hc0
        have hp : 0 < c ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hc0 _
        rw [Real.norm_eq_abs, abs_div, abs_of_pos hp, div_eq_mul_inv,
          show (c ^ ((1 : ℝ) / 3))⁻¹ = c ^ (-(1 / 3 : ℝ)) by rw [Real.rpow_neg hc0.le, one_div]]
        exact mul_le_mul_of_nonneg_right (hBbd hcn) (Real.rpow_nonneg hc0.le _)
      have h2 : ∀ᶠ c in atTop, (prob.T_V c - xiBar * c) / c ^ ((1 : ℝ) / 3) =
          (prob.T_V c - TStar c) / c ^ ((1 : ℝ) / 3) + Aopt := by
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc0
        have hp : c ^ ((1 : ℝ) / 3) ≠ 0 := (Real.rpow_pos_of_pos hc0 _).ne'
        unfold TStar; field_simp [hp]; ring
      have h_add : Tendsto (fun c => (prob.T_V c - TStar c) / c ^ ((1 : ℝ) / 3) + Aopt)
          atTop (𝓝 (0 + Aopt)) := h1.add tendsto_const_nhds
      rw [zero_add] at h_add
      exact h_add.congr' (h2.mono fun _ h => h.symm)
    have hAopt_pos : 0 < Aopt := by
      unfold Aopt
      exact mul_pos cStar_pos (abs_pos.mpr (airyZero_neg 1).ne)
    have hxiBar_pos : 0 < xiBar := by
      unfold xiBar
      exact div_pos (sq_pos_of_pos xiStar_pos) (by norm_num)
    have h1 : ∀ᶠ c : ℝ in atTop, 1 ≤ xiBar * c :=
      (tendsto_id.const_mul_atTop hxiBar_pos).eventually_ge_atTop 1
    have hB_diff_tend : Tendsto (fun c =>
        (prob.T_V c - xiBar * c) / c ^ ((1 : ℝ) / 3) - c ^ (-(1 / 3 : ℝ)) * max 0 (H c))
        atTop (𝓝 Aopt) := by
      simpa using hB_tend.sub hHo_c
    filter_upwards [h1, eventually_gt_atTop (0 : ℝ),
      hB_diff_tend.eventually (le_mem_nhds hAopt_pos)] with c hc1 hc0 hdiff
    have hp : 0 < c ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hc0 _
    have hhn : (prob.T_V c - xiBar * c) - c ^ ((1 : ℝ) / 3) * (c ^ (-(1 / 3 : ℝ)) * max 0 (H c)) ≥ 0 := by
      have hmul := mul_nonneg hp.le hdiff
      have heq : c ^ ((1 : ℝ) / 3) *
          ((prob.T_V c - xiBar * c) / c ^ ((1 : ℝ) / 3) - c ^ (-(1 / 3 : ℝ)) * max 0 (H c)) =
          (prob.T_V c - xiBar * c) - c ^ ((1 : ℝ) / 3) * (c ^ (-(1 / 3 : ℝ)) * max 0 (H c)) := by
        field_simp [hp.ne']
      linarith
    have hprod1 : c ^ ((1 : ℝ) / 3) * c ^ (-(1 / 3 : ℝ)) = 1 := by
      rw [Real.rpow_neg hc0.le, mul_inv_cancel₀ hp.ne']
    linarith [show c ^ ((1 : ℝ) / 3) * (c ^ (-(1 / 3 : ℝ)) * max 0 (H c)) = max 0 (H c) by
      rw [← mul_assoc, hprod1, one_mul]]
  obtain ⟨c_T1, hc_T1⟩ := eventually_atTop.mp hT_ge1
  refine ⟨max c_ratio c_T1, hc_ratio.trans (le_max_left _ _), fun {c η} hc hη_pos hη_le => ?_⟩
  have hc_rat : c_ratio ≤ c := (le_max_left _ _).trans hc
  have hc_pos : 0 < c := lt_of_lt_of_le zero_lt_one
    ((le_max_left 1 (12 * prob.totalShift)).trans (hc_ratio.trans hc_rat))
  have hc_shift : 12 * prob.totalShift ≤ c :=
    (le_max_right 1 (12 * prob.totalShift)).trans (hc_ratio.trans hc_rat)
  set T : ℝ := prob.T_V c - η
  have hT_lb : 1 ≤ T := by
    have h1 := hc_T1 c ((le_max_right _ _).trans hc)
    dsimp [T]
    linarith [le_max_right (0 : ℝ) (H c)]
  let X : Set ℝ := Ici T
  have h_pos_mem : ∀ t ∈ X, 0 < t := fun t ht => by
    have htT : T ≤ t := mem_Ici.mp ht
    linarith [hT_lb]
  let σ : Measure ℝ := cardyRayMeasure prob c T
  have : IsFiniteMeasureOnCompacts σ := isFiniteMeasureOnCompacts_cardyRayMeasure prob c T
  have S : DualSetupCore prob c β₀ 1 :=
    ⟨hc_pos, hc_shift, hβ₀_pos, hβ₀_half, ht0, zero_lt_one⟩
  have hXc : IsClosed X := isClosed_Ici
  have hX : X ⊆ Ici (1 : ℝ) := Ici_subset_Ici.mpr hT_lb
  have hray : ∃ τ : ℝ, Ici τ ⊆ X := ⟨T, Subset.rfl⟩
  have hσ : σ Xᶜ = 0 := by
    unfold σ cardyRayMeasure
    rw [Measure.restrict_apply (MeasurableSet.compl measurableSet_Ici), compl_inter_self, measure_empty]
  have hdens_meas : Measurable fun t => ENNReal.ofReal (prob.cardyDensity (c / 12) t) := by
    unfold FixedWeightProblem.cardyDensity
    exact ENNReal.continuous_ofReal.measurable.comp
      (continuous_const.mul (continuous_cardyV prob (c / 12))).measurable
  have hσ_eq : σ = (volume.restrict X).withDensity
      fun t => ENNReal.ofReal (prob.cardyDensity (c / 12) t) := by
    unfold σ cardyRayMeasure
    rw [restrict_withDensity measurableSet_Ici]
  have hdens_nn : ∀ t ∈ X, 0 ≤ prob.cardyDensity (c / 12) t := fun t ht => by
    unfold FixedWeightProblem.cardyDensity
    exact mul_nonneg (by positivity) (prob.cardyV_nonneg S.ha (h_pos_mem t ht).le)
  have hh_nn : ∀ t ∈ X, 0 ≤ hMaj prob.w (c / 12) β₀ t := fun t ht => by
    have h1 := wStar_le_hMaj prob.hw S.ha_pos S.hβ₀ (by linarith [S.hβ₀2]) S.hT₀ (hX ht)
    have h2 := wStar_pos S.ha_pos.le S.hβ₀ (h_pos_mem t ht).le
    linarith
  have hh : Integrable (hMaj prob.w (c / 12) β₀) σ := by
    rw [hσ_eq, integrable_withDensity_iff_integrable_smul' hdens_meas
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    have h_abs : IntegrableOn (fun t => 2 * Real.pi *
        (|hMaj prob.w (c / 12) β₀ t| * prob.cardyV (c / 12) t)) (Ioi 0) :=
      (integrableOn_abs_hMaj_V prob (β₀ := β₀) S.ha S.ha_pos).const_mul (2 * Real.pi)
    have h_mono : IntegrableOn (fun t => 2 * Real.pi *
        (|hMaj prob.w (c / 12) β₀ t| * prob.cardyV (c / 12) t)) X :=
      h_abs.mono_set (fun t ht => h_pos_mem t ht)
    refine h_mono.congr_fun (fun t ht => ?_) measurableSet_Ici
    dsimp only
    rw [ENNReal.toReal_ofReal (hdens_nn t ht), smul_eq_mul, abs_of_nonneg (hh_nn t ht),
      FixedWeightProblem.cardyDensity]
    ring
  have hh_pos_on : ∀ t ∈ X, 0 < prob.cardyDensity (c / 12) t * hMaj prob.w (c / 12) β₀ t :=
    fun t ht => by
      have ht_pos : 0 < t := h_pos_mem t ht
      have hd_pos : 0 < prob.cardyDensity (c / 12) t := by
        unfold FixedWeightProblem.cardyDensity
        exact mul_pos (by positivity) (prob.cardyV_pos S.ha ht_pos)
      have h1 := wStar_le_hMaj prob.hw S.ha_pos S.hβ₀ (by linarith [S.hβ₀2]) S.hT₀ (hX ht)
      have h2 := wStar_pos S.ha_pos.le S.hβ₀ ht_pos.le
      exact mul_pos hd_pos (h2.trans_le h1)
  have hHpos : 0 < ∫ t, hMaj prob.w (c / 12) β₀ t ∂σ := by
    have heq : ∫ t, hMaj prob.w (c / 12) β₀ t ∂σ =
        ∫ t in X, prob.cardyDensity (c / 12) t * hMaj prob.w (c / 12) β₀ t := by
      rw [hσ_eq, integral_withDensity_eq_integral_toReal_smul hdens_meas
        (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
      refine setIntegral_congr_fun measurableSet_Ici fun t ht => ?_
      rw [ENNReal.toReal_ofReal (hdens_nn t ht), smul_eq_mul]
    rw [heq]
    have h_int_X : IntegrableOn (fun t => prob.cardyDensity (c / 12) t * hMaj prob.w (c / 12) β₀ t) X := by
      have h_abs : IntegrableOn (fun t => 2 * Real.pi *
          (|hMaj prob.w (c / 12) β₀ t| * prob.cardyV (c / 12) t)) (Ioi 0) :=
        (integrableOn_abs_hMaj_V prob (β₀ := β₀) S.ha S.ha_pos).const_mul (2 * Real.pi)
      refine (h_abs.mono_set (fun t ht => h_pos_mem t ht)).congr_fun (fun t ht => ?_)
        measurableSet_Ici
      dsimp only
      rw [abs_of_nonneg (hh_nn t ht)]
      unfold FixedWeightProblem.cardyDensity; ring
    rw [setIntegral_pos_iff_support_of_nonneg_ae
      (ae_restrict_of_forall_mem measurableSet_Ici fun t ht => (hh_pos_on t ht).le) h_int_X]
    have hsup : X ⊆ Function.support (fun t => prob.cardyDensity (c / 12) t * hMaj prob.w (c / 12) β₀ t) ∩ X :=
      fun t ht => ⟨(hh_pos_on t ht).ne', ht⟩
    calc (0 : ℝ≥0∞) < volume X := by
          rw [Real.volume_Ici]; simp
      _ ≤ volume (Function.support (fun t => prob.cardyDensity (c / 12) t * hMaj prob.w (c / 12) β₀ t) ∩ X) :=
          measure_mono hsup
  have hcross : ∃ meas : AdmissibleCrossingMeasure prob (c / 12), meas.ν Xᶜ = 0 := by
    have hTV_pos : 0 < prob.T_V c := T_V_pos hc_pos hc_shift
    obtain ⟨meas, hlo, -, -⟩ := corollary_E1_exact_gap prob hc_pos hc_shift hTV_pos
    refine ⟨meas, measure_mono_null (fun t ht => ?_) hlo⟩
    rw [mem_compl_iff, mem_Ici, not_le] at ht
    change t < prob.T_V c
    linarith [hη_pos]
  obtain ⟨⟨⟨-, meas, hsupp, hdom⟩, -⟩, -⟩ :=
    theorem_E_c_reserve S hXc hX hσ hh hHpos hcross
  have hinf := theorem_E_c_reserve_testClass S hXc hX hray hσ hh hHpos hcross
  let r_tgt : ℝ := 2 * (1 - ε) * kappaRes * c ^ (-(1 / 3 : ℝ)) * η
  have h_r_le : ENNReal.ofReal r_tgt ≤ ENNReal.ofReal (reserveMax prob c β₀ X σ) := by
    rw [hinf]
    refine le_iInf fun g => le_iInf fun hg => le_iInf fun hnn => le_iInf fun hL => ?_
    have h_g_aemeas : AEMeasurable (fun t => ENNReal.ofReal (g t)) (volume.restrict X) :=
      (ENNReal.continuous_ofReal.continuousOn.comp
        (hg.cont.mono (fun t ht => (h_pos_mem t ht).le))
        (fun _ _ => mem_univ _)).aemeasurable measurableSet_Ici
    have h_int_X : IntegrableOn (fun t => g t * prob.cardyV (c / 12) t) X := by
      have h_abs : IntegrableOn (fun t => |g t| * prob.cardyV (c / 12) t) (Ioi 0) := hg.int_cardy
      refine (h_abs.mono_set (fun t ht => h_pos_mem t ht)).norm.mono' ?_ ?_
      · exact ((hg.cont.mul (continuous_cardyV prob (c / 12)).continuousOn).mono
          (fun t ht => (h_pos_mem t ht).le)).aestronglyMeasurable measurableSet_Ici
      · filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
        rw [Real.norm_eq_abs, Real.norm_of_nonneg (mul_nonneg (abs_nonneg _)
          (prob.cardyV_nonneg S.ha (h_pos_mem t ht).le)),
          abs_mul, abs_of_nonneg (prob.cardyV_nonneg S.ha (h_pos_mem t ht).le)]
    have h_lint_eq : ∫⁻ t, ENNReal.ofReal (g t) ∂σ =
        ENNReal.ofReal (2 * Real.pi * ∫ t in X, g t * prob.cardyV (c / 12) t) := by
      rw [hσ_eq, lintegral_withDensity_eq_lintegral_mul₀ hdens_meas.aemeasurable h_g_aemeas]
      simp only [Pi.mul_apply]
      have h_eq1 : ∫⁻ t in X, ENNReal.ofReal (prob.cardyDensity (c / 12) t) * ENNReal.ofReal (g t) =
          ∫⁻ t in X, ENNReal.ofReal (2 * Real.pi * (g t * prob.cardyV (c / 12) t)) := by
        refine setLIntegral_congr_fun measurableSet_Ici fun t ht => ?_
        rw [← ENNReal.ofReal_mul (hdens_nn t ht)]
        congr 1; unfold FixedWeightProblem.cardyDensity; ring
      rw [h_eq1, ← ofReal_integral_eq_lintegral_ofReal (h_int_X.const_mul (2 * Real.pi))
        (ae_restrict_of_forall_mem measurableSet_Ici fun t ht =>
          mul_nonneg (by positivity) (mul_nonneg (hnn t ht)
            (prob.cardyV_nonneg S.ha (h_pos_mem t ht).le)))]
      rw [integral_const_mul]
    have hray_pos : 0 < ∫ t in X, g t * prob.cardyV (c / 12) t := by
      rw [h_lint_eq] at hL
      by_contra hle
      push Not at hle
      have h0 : 2 * Real.pi * ∫ t in X, g t * prob.cardyV (c / 12) t ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) hle
      rw [ENNReal.ofReal_of_nonpos h0] at hL
      exact lt_irrefl _ hL
    have h_rat := h_ratio hc_rat hη_pos hη_le hg hnn hray_pos
    have h_gvac_eq : -prob.gVac (c / 12) g =
        2 * Real.pi * ∫ t in Ioi (0 : ℝ), g t * prob.cardyV (c / 12) t := by
      unfold FixedWeightProblem.gVac; ring
    rw [h_lint_eq, h_gvac_eq, ← ENNReal.ofReal_div_of_pos (mul_pos (by positivity) hray_pos)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h_cancel : (2 * Real.pi * ∫ t in Ioi (0 : ℝ), g t * prob.cardyV (c / 12) t) /
        (2 * Real.pi * ∫ t in X, g t * prob.cardyV (c / 12) t) =
        (∫ t in Ioi (0 : ℝ), g t * prob.cardyV (c / 12) t) /
          (∫ t in X, g t * prob.cardyV (c / 12) t) :=
      mul_div_mul_left _ _ (by positivity)
    rw [h_cancel]
    linarith [show r_tgt = (1 - ε) * (2 * kappaRes) * c ^ (-(1 / 3 : ℝ)) * η by dsimp [r_tgt]; ring]
  have hr_le_real : r_tgt ≤ reserveMax prob c β₀ X σ :=
    (ENNReal.ofReal_le_ofReal_iff (theorem_E_c_reserve S hXc hX hσ hh hHpos hcross).1.1.1).mp h_r_le
  refine ⟨meas, hsupp, (Measure.le_iff.mpr fun s _ => ?_).trans hdom⟩
  simp only [smul_apply, smul_eq_mul]
  exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hr_le_real) (by simp)

/-- Specialization of `int_reserve_measure` to `η ∈ (0, 1]` (`int:res-meas`, Theorem INT-2). -/
theorem int_reserve_measure_const (prob : FixedWeightProblem) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ c₀ : ℝ, max 1 (12 * prob.totalShift) ≤ c₀ ∧
      ∀ {c η : ℝ}, c₀ ≤ c → 0 < η → η ≤ 1 →
        ∃ meas : AdmissibleCrossingMeasure prob (c / 12),
          meas.ν (Ici (prob.T_V c - η))ᶜ = 0 ∧
          ENNReal.ofReal (2 * (1 - ε) * kappaRes * c ^ (-(1 / 3 : ℝ)) * η) •
            cardyRayMeasure prob c (prob.T_V c - η) ≤ meas.ν := by
  have hHo : (fun _ : ℝ => (1 : ℝ)) =o[atTop] fun c : ℝ => c ^ ((1 : ℝ) / 3) := by
    refine Asymptotics.isLittleO_of_tendsto' ?_ ?_
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc h0
      exact absurd h0 (Real.rpow_pos_of_pos hc _).ne'
    · simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).congr'
        (by filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
            rw [Real.rpow_neg hc.le, one_div])
  exact int_reserve_measure prob hε0 hε1 hHo

/-- **Corollary INT-2.2** (`int:strict-weak`, `integrality.tex`): in setting `(H_w)`,
`T_weak(c̃) = T_V(c̃)` for all sufficiently large `c̃`. -/
theorem int_strict_weak (prob : FixedWeightProblem) :
    ∀ᶠ c in atTop, prob.T_weak c = prob.T_V c := by
  obtain ⟨c₀, hc₀, h_low⟩ := int_reserve_lower_const prob
    (show (0 : ℝ) < 1 / 2 by norm_num) (show (1 / 2 : ℝ) < 1 by norm_num)
  filter_upwards [eventually_ge_atTop c₀] with c hc
  have hc_pos : 0 < c := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans (hc₀.trans hc))
  have hc_shift : 12 * prob.totalShift ≤ c :=
    (le_max_right 1 (12 * prob.totalShift)).trans (hc₀.trans hc)
  have hle : prob.T_weak c ≤ prob.T_V c := prob.T_weak_le_T_V hc_shift
  have hge : prob.T_V c ≤ prob.T_weak c := by
    by_contra hlt
    push Not at hlt
    have hne : {T : ℝ | 0 < T ∧ ∃ g, prob.IsWeaklyFeasible (c / 12) T g}.Nonempty := by
      obtain ⟨T, hT⟩ := prob.feasible_nonempty hc_shift
      exact ⟨T, hT.1, hT.2.imp fun _ hg => hg.isWeaklyFeasible⟩
    obtain ⟨τ, ⟨hτ_pos, g, hg_wf⟩, hτ_lt⟩ := exists_lt_of_csInf_lt hne hlt
    obtain ⟨hg_tc, hg_nz, hg_vac, hg_nn⟩ := hg_wf
    let η : ℝ := min 1 (prob.T_V c - τ)
    have hη_pos : 0 < η := lt_min one_pos (by linarith)
    have hη_le : η ≤ 1 := min_le_left _ _
    have h_nn' : ∀ t : ℝ, prob.T_V c - η ≤ t → 0 ≤ g t := fun t ht =>
      hg_nn t (by linarith [min_le_right (1 : ℝ) (prob.T_V c - τ)])
    have h_ratio := h_low hc hη_pos hη_le hg_tc hg_nz h_nn'
    have hM_pos : 0 < prob.cardyNorm (c / 12) g :=
      cardyNorm_pos_of_nonzero_general prob (by linarith) hg_tc hg_nz
    have h_lhs_pos : 0 < (1 - 1 / 2) * kappaRes * c ^ (-(1 / 3 : ℝ)) * η :=
      mul_pos (mul_pos (mul_pos (by norm_num) kappaRes_pos) (Real.rpow_pos_of_pos hc_pos _)) hη_pos
    have hI_pos : 0 < ∫ t in Ioi (0 : ℝ), g t * prob.cardyV (c / 12) t :=
      (div_pos_iff_of_pos_right hM_pos).mp (lt_of_lt_of_le h_lhs_pos h_ratio)
    have hvac_neg : prob.gVac (c / 12) g < 0 := by
      unfold FixedWeightProblem.gVac
      nlinarith [Real.pi_pos]
    linarith
  exact le_antisymm hle hge

end FormalResearch.ModularBootstrap.Integrality

/-- info: 'FormalResearch.ModularBootstrap.Integrality.int_reserve_ray_ratio_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Integrality.int_reserve_ray_ratio_lower

/-- info: 'FormalResearch.ModularBootstrap.Integrality.int_reserve_measure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Integrality.int_reserve_measure

/-- info: 'FormalResearch.ModularBootstrap.Integrality.int_reserve_measure_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Integrality.int_reserve_measure_const

/-- info: 'FormalResearch.ModularBootstrap.Integrality.int_strict_weak' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Integrality.int_strict_weak
