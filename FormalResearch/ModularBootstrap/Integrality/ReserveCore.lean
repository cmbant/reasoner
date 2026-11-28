module

public import FormalResearch.ModularBootstrap.Blowup.NormLimitSVariable
public import FormalResearch.ModularBootstrap.Duality.Primal.OneLevelClusters
public import FormalResearch.ModularBootstrap.Duality.Primal.HbMassMoments
public import FormalResearch.ModularBootstrap.Stability.ClarkStabilityLimit

/-!
# Reserve linear growth lower bound (`integrality.tex`, `int:reserve` / `int:hb-reserve`(a) at `m₀ = 1`)

Proves the normalized vacuum-pairing lower bound of Theorem INT-2 (`int:reserve`) in setting `(H_w)`
(`prob : FixedWeightProblem`), uniformly for `0 < η ≤ H(c̃)` with `H(c̃) = o(c̃^{1/3})` (no lower
restriction on `η`):

* `kappaRes`: `(2 * cStar * LStar)⁻¹ = 3 * betaTip / (4 * xiStar * LStar)`.
* `jacRatio_tendsto_one`: `jAiry c t / (-deriv (virasoroDeltaChart c) (chartUT c t)) → 1`
  uniformly on bounded Airy windows `|uAiry c t| ≤ M`.
* `int_reserve_lower_testClass`: for fixed `prob`, `ε ∈ (0, 1)`, and `H =o[atTop] fun c => c ^ (1 / 3)`,
  for all sufficiently large `c`, all `0 < η ≤ H c`, and all nonzero `g ∈ TestClass prob (c / 12)`
  nonnegative on `[T_V c - η, ∞)`,
  `(1 - ε) * kappaRes * c ^ (-(1 / 3)) * η * M[g] ≤ ∫ t in Ioi 0, g t * V(t)`.
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

/-! ### 1. Reserve slope constant `κ_*^res` and Airy extremal derivative -/

/-- The Airy reserve slope constant `κ_*^res = 1 / (2 c_* L_*) = 3 β / (4 ξ_* L_*)`. -/
noncomputable def kappaRes : ℝ := (2 * cStar * LStar)⁻¹

lemma kappaRes_pos : 0 < kappaRes := by
  unfold kappaRes
  have := cStar_pos
  have := LStar_pos
  positivity

lemma kappaRes_eq_beta : kappaRes = 3 * betaTip / (4 * xiStar * LStar) := by
  unfold kappaRes cStar
  have := xiStar_pos.ne'
  have := betaTip_pos.ne'
  have := LStar_pos.ne'
  field_simp
  norm_num

/-- The derivative of the `s`-variable Airy extremal profile `normProfileS airyExtremal`
at `s₁ = -a₁ / β` is `β² Ai'(a₁)² / (2 L_*) > 0`. -/
lemma deriv_normProfileS_airyExtremal_at :
    deriv (normProfileS airyExtremal) (((-airyZero 1 / betaTip : ℝ) : ℂ)) =
      ((betaTip ^ 2 * airyAi' (airyZero 1) ^ 2 / (2 * LStar) : ℝ) : ℂ) := by
  have hb := betaTip_pos
  have hL := LStar_pos
  have h_mass : profileMass airyExtremal = 2 * LStar := by
    rw [profileMass_airyExtremal, two_mul_LStar_eq_quantC1Mass]
  let s₁ : ℂ := ((-airyZero 1 / betaTip : ℝ) : ℂ)
  have hs₁ : -((betaTip : ℝ) : ℂ) * s₁ = (airyZero 1 : ℂ) := by
    dsimp [s₁]; push_cast; field_simp [hb.ne']
  have h_lin : HasDerivAt (fun s : ℂ => -((betaTip : ℝ) : ℂ) * s)
      (-((betaTip : ℝ) : ℂ)) s₁ := by
    simpa using (hasDerivAt_id s₁).const_mul (-((betaTip : ℝ) : ℂ))
  have h_ext : HasDerivAt airyExtremal (deriv airyExtremal (airyZero 1 : ℂ))
      (-((betaTip : ℝ) : ℂ) * s₁) := by
    rw [hs₁]
    exact (differentiable_airyExtremal _).hasDerivAt
  have h_comp : HasDerivAt
      (fun s : ℂ => ((betaTip : ℝ) : ℂ) * ((profileMass airyExtremal : ℂ)⁻¹ *
        airyExtremal (-((betaTip : ℝ) : ℂ) * s)))
      (((betaTip : ℝ) : ℂ) * ((profileMass airyExtremal : ℂ)⁻¹ *
        (deriv airyExtremal (airyZero 1 : ℂ) * -((betaTip : ℝ) : ℂ)))) s₁ :=
    ((h_ext.comp s₁ h_lin).const_mul ((profileMass airyExtremal : ℂ)⁻¹)).const_mul
      ((betaTip : ℝ) : ℂ)
  have h_fn : normProfileS airyExtremal =
      fun s : ℂ => ((betaTip : ℝ) : ℂ) * ((profileMass airyExtremal : ℂ)⁻¹ *
        airyExtremal (-((betaTip : ℝ) : ℂ) * s)) := by
    funext s; unfold normProfileS normProfile; push_cast; ring
  rw [show (((-airyZero 1 / betaTip : ℝ) : ℂ)) = s₁ from rfl, h_fn, h_comp.deriv,
    airyExtremal_deriv_a1, h_mass]
  push_cast
  field_simp [hb.ne', hL.ne']

/-! ### 2. Chart derivative and Jacobian ratio limits -/

/-- On any bounded window `|u| ≤ M`, `-deriv (virasoroDeltaChart c) u / (cStar * c^{1/3}) → 1`
uniformly as `c → ∞`. -/
lemma deriv_virasoroDeltaChart_div_tendsto (M : ℝ) (_hM : 0 ≤ M) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ c : ℝ in atTop, ∀ u : ℝ, |u| ≤ M →
      |-deriv (virasoroDeltaChart c) u / (cStar * c ^ ((1 : ℝ) / 3)) - 1| ≤ ε := by
  intro ε hε
  have hcS := cStar_pos
  have hcont : ContinuousAt (deriv virasoroXiInf) 0 :=
    (virasoroXiInf_an.deriv 0 (mem_ball_self virasoroRUInf_pos)).continuousAt
  obtain ⟨δ, hδ, hδ_ball⟩ := Metric.continuousAt_iff.mp hcont (ε * cStar) (mul_pos hε hcS)
  have hac : ∀ᶠ c : ℝ in atTop, M ≤ virasoroAC c ^ 2 := by
    have h1 : Tendsto (fun c : ℝ => virasoroAC c ^ 2) atTop atTop :=
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).const_mul_atTop
        (mul_pos two_pos (pow_pos virasoroBV_pos 2))).congr'
        (by filter_upwards [eventually_ge_atTop (0 : ℝ)] with c hc; rw [virasoroAC_sq c hc])
    exact h1.eventually_ge_atTop M
  have hsmall : ∀ᶠ c : ℝ in atTop, M * c ^ (-(2 / 3 : ℝ)) < δ := by
    have ht : Tendsto (fun c : ℝ => M * c ^ (-(2 / 3 : ℝ))) atTop (𝓝 0) := by
      simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).const_mul M
    exact ht.eventually (gt_mem_nhds hδ)
  filter_upwards [eventually_gt_atTop (0 : ℝ), hac, hsmall] with c hc0 hMac hmδ u hu
  have hu_ac : |u| ≤ virasoroAC c ^ 2 := hu.trans hMac
  have hd := virasoroDeltaChart_hasDerivAt hc0 hu_ac
  have hcp_ne : c ^ ((1 : ℝ) / 3) ≠ 0 := (Real.rpow_pos_of_pos hc0 _).ne'
  have hc23_nn : 0 ≤ c ^ (-(2 / 3 : ℝ)) := Real.rpow_nonneg hc0.le _
  have hw_dist : dist ((u * c ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) 0 < δ := by
    rw [dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg hc23_nn]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hu hc23_nn) hmδ
  have hxi := hδ_ball hw_dist
  rw [Complex.dist_eq, virasoroXiInf_deriv_zero] at hxi
  have hre : |(deriv virasoroXiInf ((u * c ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ)).re + cStar| < ε * cStar := by
    have heq : (deriv virasoroXiInf ((u * c ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ)).re + cStar =
        ((deriv virasoroXiInf ((u * c ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) - (-(cStar : ℂ))).re) := by
      simp only [Complex.sub_re, Complex.neg_re, Complex.ofReal_re]; ring
    rw [heq]
    exact (abs_re_le_norm _).trans_lt hxi
  have h_div_eq : -deriv (virasoroDeltaChart c) u / (cStar * c ^ ((1 : ℝ) / 3)) - 1 =
      -((deriv virasoroXiInf ((u * c ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ)).re + cStar) / cStar := by
    rw [hd.deriv]
    field_simp [hcS.ne', hcp_ne]
    ring
  rw [h_div_eq, abs_div, abs_neg, abs_of_pos hcS, div_le_iff₀ hcS]
  exact hre.le

/-- On any bounded Airy window `|uAiry c t| ≤ M`, `jacRatio c t → 1` uniformly as `c → ∞`. -/
lemma jacRatio_tendsto_one (M : ℝ) (hM : 0 ≤ M) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ c : ℝ in atTop, ∀ t : ℝ, 0 < t → |uAiry c t| ≤ M →
      |jacRatio c t - 1| ≤ ε := by
  intro ε hε
  let δ : ℝ := min (1 / 2) (ε / 4)
  have hδ : 0 < δ := lt_min (by norm_num) (by linarith)
  have hδ2 : δ ≤ 1 / 2 := min_le_left _ _
  have hcS := cStar_pos
  have hb := betaTip_pos
  have hxi := xiStar_pos
  obtain ⟨C_ut, c_ut, _, _, hC_ut⟩ := chartUT_sub_uAiry_err hM
  have hJ_ev : ∀ᶠ c : ℝ in atTop, M * epsAiry c / (betaTip * xiStar) ≤ δ := by
    have ht : Tendsto (fun c : ℝ => M * epsAiry c / (betaTip * xiStar)) atTop (𝓝 0) := by
      have heps : Tendsto epsAiry atTop (𝓝 0) := by
        have h := tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)
        refine h.congr' (Eventually.of_forall fun x => ?_)
        unfold epsAiry; ring_nf
      simpa using (heps.const_mul M).div_const (betaTip * xiStar)
    exact ht.eventually (ge_mem_nhds hδ)
  filter_upwards [eventually_ge_atTop (max 1 c_ut), hJ_ev,
    deriv_virasoroDeltaChart_div_tendsto (M + 1) (by linarith) δ hδ] with c hc hJ hD t htp huM
  have hc_pos : 0 < c := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hc)
  have hc_ut : c_ut ≤ c := (le_max_right _ _).trans hc
  obtain ⟨hchart_abs, -, -⟩ := hC_ut hc_ut htp huM
  have hJ_bd := jAiry_bounds hc_pos huM
  have hcS_pos : 0 < cStar * c ^ ((1 : ℝ) / 3) := mul_pos hcS (Real.rpow_pos_of_pos hc_pos _)
  have hJ_ratio : |jAiry c t / (cStar * c ^ ((1 : ℝ) / 3)) - 1| ≤ δ := by
    have heq : jAiry c t / (cStar * c ^ ((1 : ℝ) / 3)) - 1 =
        (jAiry c t - cStar * c ^ ((1 : ℝ) / 3)) / (cStar * c ^ ((1 : ℝ) / 3)) := by
      field_simp [hcS_pos.ne']
    rw [heq, abs_div, abs_of_pos hcS_pos, div_le_iff₀ hcS_pos]
    calc |jAiry c t - cStar * c ^ ((1 : ℝ) / 3)|
        ≤ cStar * c ^ ((1 : ℝ) / 3) * (M * epsAiry c / (betaTip * xiStar)) := hJ_bd
      _ ≤ cStar * c ^ ((1 : ℝ) / 3) * δ := mul_le_mul_of_nonneg_left hJ hcS_pos.le
      _ = δ * (cStar * c ^ ((1 : ℝ) / 3)) := by ring
  have hD_ratio : |-deriv (virasoroDeltaChart c) (chartUT c t) / (cStar * c ^ ((1 : ℝ) / 3)) - 1| ≤ δ :=
    hD (chartUT c t) hchart_abs
  set a : ℝ := jAiry c t / (cStar * c ^ ((1 : ℝ) / 3))
  set b : ℝ := -deriv (virasoroDeltaChart c) (chartUT c t) / (cStar * c ^ ((1 : ℝ) / 3))
  have hb_lo : 1 / 2 ≤ b := by linarith [(abs_le.mp hD_ratio).1]
  have hb_pos : 0 < b := by linarith
  have h_eq : jacRatio c t = a / b := by
    unfold jacRatio; dsimp [a, b]; field_simp [hcS_pos.ne']
  rw [h_eq]
  have h_sub : |a / b - 1| = |a - b| / b := by
    rw [show a / b - 1 = (a - b) / b by field_simp [hb_pos.ne'], abs_div, abs_of_pos hb_pos]
  rw [h_sub, div_le_iff₀ hb_pos]
  have hab : |a - b| ≤ 2 * δ := by
    have : a - b = (a - 1) - (b - 1) := by ring
    rw [this]; exact (abs_sub _ _).trans (by linarith)
  have h4δ : 2 * δ ≤ ε / 2 := by linarith [min_le_right (1 / 2 : ℝ) (ε / 4)]
  nlinarith

/-! ### 3. Main lower reserve theorem (`int:reserve` / `int:hb-reserve`(a) at `m₀ = 1`) -/

/-- **Theorem INT-2, lower slope (`int:reserve`, `int:res-bound`; `int:hb-reserve`(a) at `m₀ = 1`)**:
for every fixed-weight problem `prob`, `ε ∈ (0, 1)`, and `H =o[atTop] fun c => c ^ (1 / 3)`,
there exists `c₀` such that for all `c ≥ c₀`, all `η` with `0 < η ≤ H c`, and all nonzero
`g ∈ TestClass prob (c / 12)` nonnegative on `[T_V c - η, ∞)`,
`(1 - ε) * kappaRes * c ^ (-(1 / 3)) * η * M[g] ≤ ∫ t in Ioi 0, g t * prob.cardyV (c / 12) t`.
No lower restriction on `η` is imposed. -/
theorem int_reserve_lower_testClass (prob : FixedWeightProblem) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) {H : ℝ → ℝ}
    (hHo : H =o[atTop] fun c : ℝ => c ^ ((1 : ℝ) / 3)) :
    ∃ c₀ : ℝ, max 1 (12 * prob.totalShift) ≤ c₀ ∧
      ∀ {c η : ℝ}, c₀ ≤ c → 0 < η → η ≤ H c →
        ∀ {g : ℝ → ℝ}, TestClass prob (c / 12) g → (∃ t ≥ 0, g t ≠ 0) →
          (∀ t : ℝ, prob.T_V c - η ≤ t → 0 ≤ g t) →
          (1 - ε) * kappaRes * c ^ (-(1 / 3 : ℝ)) * η * prob.cardyNorm (c / 12) g ≤
            ∫ t in Ioi (0 : ℝ), g t * prob.cardyV (c / 12) t := by
  by_contra hcontra
  push Not at hcontra
  have hpick : ∀ n : ℕ, ∃ c η : ℝ, ∃ g : ℝ → ℝ,
      max (n : ℝ) (max 1 (12 * prob.totalShift)) ≤ c ∧
      0 < η ∧ η ≤ H c ∧
      TestClass prob (c / 12) g ∧ (∃ t ≥ 0, g t ≠ 0) ∧
      (∀ t : ℝ, prob.T_V c - η ≤ t → 0 ≤ g t) ∧
      ∫ t in Ioi (0 : ℝ), g t * prob.cardyV (c / 12) t <
        (1 - ε) * kappaRes * c ^ (-(1 / 3 : ℝ)) * η * prob.cardyNorm (c / 12) g := fun n => by
    obtain ⟨c, η, hc, hη1, hη2, g, hg⟩ :=
      hcontra (max (n : ℝ) (max 1 (12 * prob.totalShift))) (le_max_right _ _)
    exact ⟨c, η, g, hc, hη1, hη2, hg⟩
  choose c η g_raw h_cn hη_pos hη_le h_tc h_ne h_nn h_viol using hpick
  have hc_tend : Tendsto c atTop atTop :=
    tendsto_atTop_mono (fun n => (le_max_left (n : ℝ) _).trans (h_cn n)) tendsto_natCast_atTop_atTop
  have hshift_n : ∀ n, 12 * prob.totalShift ≤ c n := fun n =>
    (le_max_right 1 _).trans ((le_max_right (n : ℝ) _).trans (h_cn n))
  have hc_ge1 : ∀ n, 1 ≤ c n := fun n =>
    (le_max_left 1 _).trans ((le_max_right (n : ℝ) _).trans (h_cn n))
  have hc_pos : ∀ n, 0 < c n := fun n => lt_of_lt_of_le zero_lt_one (hc_ge1 n)
  have hM_raw_pos : ∀ n, 0 < prob.cardyNorm (c n / 12) (g_raw n) := fun n =>
    cardyNorm_pos_of_nonzero_general prob (by linarith [hshift_n n]) (h_tc n) (h_ne n)
  -- Normalise `g n := M[g_raw n]⁻¹ • g_raw n` so `M[g n] = 1`.
  let g : ℕ → ℝ → ℝ := fun n t => (prob.cardyNorm (c n / 12) (g_raw n))⁻¹ * g_raw n t
  have hg_tc : ∀ n, TestClass prob (c n / 12) (g n) := fun n =>
    (h_tc n).smul ((prob.cardyNorm (c n / 12) (g_raw n))⁻¹)
  have hg_M : ∀ n, prob.cardyNorm (c n / 12) (g n) = 1 := fun n => by
    unfold FixedWeightProblem.cardyNorm
    have hi_inv : 0 < (prob.cardyNorm (c n / 12) (g_raw n))⁻¹ := inv_pos.mpr (hM_raw_pos n)
    have heq : (fun t => |g n t| * prob.cardyV (c n / 12) t) =
        fun t => (prob.cardyNorm (c n / 12) (g_raw n))⁻¹ * (|g_raw n t| * prob.cardyV (c n / 12) t) := by
      ext t; dsimp [g]; rw [abs_mul, abs_of_pos hi_inv]; ring
    rw [heq, integral_const_mul]
    exact inv_mul_cancel₀ (hM_raw_pos n).ne'
  have hg_nn : ∀ n t, prob.T_V (c n) - η n ≤ t → 0 ≤ g n t := fun n t ht =>
    mul_nonneg (inv_nonneg.mpr (hM_raw_pos n).le) (h_nn n t ht)
  let B : ℕ → ℝ := fun n => prob.T_V (c n)
  let T : ℕ → ℝ := fun n => B n - η n
  -- Attaining crossing measure `meas n` at gap `B n = prob.T_V (c n)`
  have hTV_ev : ∀ᶠ n in atTop, 0 < B n := by
    filter_upwards [hc_tend.eventually_gt_atTop 0, hc_tend.eventually_ge_atTop (12 * prob.totalShift)] with n hc0 hc12
    exact T_V_pos hc0 hc12
  have hI_nonneg : ∀ᶠ n in atTop, 0 ≤ ∫ t in Ioi (0 : ℝ), g n t * prob.cardyV (c n / 12) t := by
    filter_upwards [hTV_ev] with n hTV_n
    obtain ⟨meas, hmeas_lo, -, -⟩ := corollary_E1_exact_gap prob (hc_pos n) (hshift_n n) hTV_n
    have ha : prob.totalShift ≤ c n / 12 := by linarith [hshift_n n]
    have ha0 : 0 < c n / 12 := by linarith [hc_pos n]
    obtain ⟨_, hfw⟩ := lemma_fwX_one_sided_unconditional prob ha ha0 meas (hg_tc n)
      (T := B n) (fun t ht => hg_nn n t (by linarith [show B n = prob.T_V (c n) from rfl, hη_pos n]))
    have hsupp : meas.ν (Ici (B n))ᶜ = 0 := by
      rw [show (Ici (B n))ᶜ = Iio (B n) by ext t; simp]
      exact hmeas_lo
    have h_ae_nn : ∀ᵐ t ∂meas.ν, 0 ≤ g n t := by
      filter_upwards [ae_mem_of_null hsupp] with t ht
      exact hg_nn n t (by linarith [show B n = prob.T_V (c n) from rfl, hη_pos n, show B n ≤ t from ht])
    have h_int_nn : 0 ≤ ∫ t in Ici (0 : ℝ), g n t ∂meas.ν := by
      rw [Duality.restrict_Ici_eq_self meas]
      exact integral_nonneg_of_ae h_ae_nn
    have hvac_pos : 0 ≤ -prob.gVac (c n / 12) (g n) := by linarith
    have hgvac : -prob.gVac (c n / 12) (g n) =
        2 * Real.pi * ∫ t in Ioi (0 : ℝ), g n t * prob.cardyV (c n / 12) t := by
      unfold FixedWeightProblem.gVac; ring
    rw [hgvac] at hvac_pos
    exact (mul_nonneg_iff_of_pos_left (mul_pos two_pos Real.pi_pos)).mp hvac_pos
  -- Normalized vacuum integral `slack n` and `o(1)` convergence
  let slack : ℕ → ℝ := fun n => ∫ t in Ioi (0 : ℝ), g n t * prob.cardyV (c n / 12) t
  have hslack_eq : ∀ n, slack n =
      (prob.cardyNorm (c n / 12) (g_raw n))⁻¹ *
        ∫ t in Ioi (0 : ℝ), g_raw n t * prob.cardyV (c n / 12) t := fun n => by
    dsimp [slack, g]
    have heq : (fun t => (prob.cardyNorm (c n / 12) (g_raw n))⁻¹ * g_raw n t * prob.cardyV (c n / 12) t) =
        fun t => (prob.cardyNorm (c n / 12) (g_raw n))⁻¹ * (g_raw n t * prob.cardyV (c n / 12) t) := by
      ext t; ring
    rw [heq, integral_const_mul]
  have hslack_lt : ∀ n, slack n < (1 - ε) * kappaRes * (c n) ^ (-(1 / 3 : ℝ)) * η n := fun n => by
    rw [hslack_eq]
    have hM := hM_raw_pos n
    have hv := mul_lt_mul_of_pos_left (h_viol n) (inv_pos.mpr hM)
    rwa [show (prob.cardyNorm (c n / 12) (g_raw n))⁻¹ *
          ((1 - ε) * kappaRes * (c n) ^ (-(1 / 3 : ℝ)) * η n * prob.cardyNorm (c n / 12) (g_raw n)) =
          (1 - ε) * kappaRes * (c n) ^ (-(1 / 3 : ℝ)) * η n by field_simp [hM.ne']] at hv
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
  have hslack_tend : Tendsto slack atTop (𝓝 0) := by
    have hmul : Tendsto (fun n => (1 - ε) * kappaRes * (c n) ^ (-(1 / 3 : ℝ)) * η n) atTop (𝓝 0) :=
      ((hη_div_tend.const_mul ((1 - ε) * kappaRes)).congr fun n => by ring)
        |>.trans (by simp)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmul
      hI_nonneg (Eventually.of_forall fun n => (hslack_lt n).le)
  have hsf : ∀ᶠ n in atTop, IsSlackFeasible prob (c n / 12) (T n) (slack n) (g n) := by
    filter_upwards [hI_nonneg] with n _
    refine ⟨hg_tc n, by rw [hg_M n]; exact one_pos, ?_, hg_nn n⟩
    rw [hg_M n, mul_one]
  -- Threshold asymptote for `T n = B n - η n`
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
      exact show |B n - TStar (c n)| * (c n) ^ (-(1 / 3 : ℝ)) ≤ B₀ * (c n) ^ (-(1 / 3 : ℝ)) from
        mul_le_mul_of_nonneg_right (hBbd hcn) (Real.rpow_nonneg hc0.le _)
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
  have hS_hi : ∃ S_hi : ℝ, ∀ᶠ n in atTop, (T n - xiBar * c n) / (c n) ^ ((1 : ℝ) / 3) ≤ S_hi :=
    ⟨Aopt + 1, hS_tend.eventually (ge_mem_nhds (by linarith))⟩
  -- Apply `airy_blnorm_s`
  obtain ⟨D⟩ := proposition_P_of_problem prob
  have hbl := airy_blnorm_s D hc_tend hslack_tend hI_nonneg hsf hS_hi
  have hAopt_eq : -cStar * airyZero 1 = Aopt := by
    unfold Aopt; rw [abs_of_neg (airyZero_neg 1)]; ring
  have hS_cond : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop,
      (T n - xiBar * c n) / (c n) ^ ((1 : ℝ) / 3) ≤ -cStar * airyZero 1 + δ := fun δ hδ => by
    rw [hAopt_eq]
    exact hS_tend.eventually (ge_mem_nhds (by linarith))
  obtain ⟨-, huT_airy, -, hderiv_lim, -, -, -⟩ := hbl.2 hS_cond
  have huB_airy : Tendsto (fun n => uAiry (c n) (B n)) atTop (𝓝 (airyZero 1)) :=
    uAiry_T_V_tendsto prob hc_tend
  -- Chart images `u_T`, `u_B` and `s`-coordinates `s_T ≤ s_B`
  let u_T : ℕ → ℝ := fun n => chartUT (c n) (T n)
  let u_B : ℕ → ℝ := fun n => chartUT (c n) (B n)
  let s_T : ℕ → ℝ := fun n => -(u_T n) / betaTip
  let s_B : ℕ → ℝ := fun n => -(u_B n) / betaTip
  let M_win : ℝ := |airyZero 1| + 1
  let M_dom : ℝ := M_win + 1
  have hM_win : 0 ≤ M_win := by positivity
  have hM_dom : 0 ≤ M_dom := by positivity
  obtain ⟨C_ut, c_ut, _, _, hC_ut⟩ := chartUT_sub_uAiry_err hM_win
  have huT_bd : ∀ᶠ n in atTop, |uAiry (c n) (T n)| ≤ M_win := by
    filter_upwards [huT_airy.eventually (Metric.ball_mem_nhds (airyZero 1) one_pos)] with n hn
    rw [Real.dist_eq] at hn
    exact abs_le.mpr ⟨by linarith [(abs_lt.mp hn).1, neg_abs_le (airyZero 1)],
      by linarith [(abs_lt.mp hn).2, le_abs_self (airyZero 1)]⟩
  have huB_bd : ∀ᶠ n in atTop, |uAiry (c n) (B n)| ≤ M_win := by
    filter_upwards [huB_airy.eventually (Metric.ball_mem_nhds (airyZero 1) one_pos)] with n hn
    rw [Real.dist_eq] at hn
    exact abs_le.mpr ⟨by linarith [(abs_lt.mp hn).1, neg_abs_le (airyZero 1)],
      by linarith [(abs_lt.mp hn).2, le_abs_self (airyZero 1)]⟩
  have hT_pos : ∀ᶠ n in atTop, 0 < T n :=
    eventually_pos_of_uAiry_tendsto hc_tend huT_airy
  have hut_err_tend : Tendsto (fun n => C_ut * (c n) ^ (-(2 / 3 : ℝ))) atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp hc_tend).const_mul C_ut
  have hu_T_tend : Tendsto u_T atTop (𝓝 (airyZero 1)) := by
    have hdiff : Tendsto (fun n => u_T n - uAiry (c n) (T n)) atTop (𝓝 0) := by
      refine squeeze_zero_norm' ?_ hut_err_tend
      filter_upwards [hc_tend.eventually_ge_atTop c_ut, hT_pos, huT_bd] with n hcn hTp hu
      have h3 := (hC_ut hcn hTp hu).2.2
      rwa [abs_sub_comm] at h3
    simpa using hdiff.add huT_airy
  have hu_B_tend : Tendsto u_B atTop (𝓝 (airyZero 1)) := by
    have hdiff : Tendsto (fun n => u_B n - uAiry (c n) (B n)) atTop (𝓝 0) := by
      refine squeeze_zero_norm' ?_ hut_err_tend
      filter_upwards [hc_tend.eventually_ge_atTop c_ut, hTV_ev, huB_bd] with n hcn hBp hu
      have h3 := (hC_ut hcn hBp hu).2.2
      rwa [abs_sub_comm] at h3
    simpa using hdiff.add huB_airy
  let s₁ : ℝ := -airyZero 1 / betaTip
  have hb_pos := betaTip_pos
  have hs_T_tend : Tendsto s_T atTop (𝓝 s₁) := by
    have heq : (fun n => s_T n) = fun n => -u_T n / betaTip := rfl
    simpa [s₁] using (hu_T_tend.neg).div_const betaTip
  have hs_B_tend : Tendsto s_B atTop (𝓝 s₁) := by
    simpa [s₁] using (hu_B_tend.neg).div_const betaTip
  -- Slope parameters `δ₀`, radius `m_ball`
  let w₀ : ℝ := airyAi' (airyZero 1) ^ 2
  have hw₀_ne : airyAi' (airyZero 1) ≠ 0 := by
    intro h0
    have := airyNodeWeight_pos 0
    unfold airyNodeWeight airyNode at this
    rw [show 0 + 1 = 1 from rfl, h0] at this
    simp at this
  have hw₀_pos : 0 < w₀ := sq_pos_of_ne_zero hw₀_ne
  let slope₀ : ℝ := betaTip ^ 2 * w₀ / (2 * LStar)
  have hslope₀_pos : 0 < slope₀ := by have := LStar_pos; positivity
  -- Choose `δ_err ∈ (0, 1/2)` small enough so `(1 - δ_err)^4 > 1 - ε`.
  obtain ⟨δ_err, hδ_pos, hδ_lt_half, hδ_pow4⟩ :
      ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 2 ∧ (1 - ε) < (1 - δ) ^ 4 := by
    have hcont : ContinuousAt (fun x : ℝ => (1 - x) ^ 4) 0 := by fun_prop
    obtain ⟨ηd, hηd_pos, hηd⟩ := Metric.continuousAt_iff.mp hcont (1 - (1 - ε)) (by linarith)
    refine ⟨min (1 / 4) (ηd / 2), lt_min (by norm_num) (half_pos hηd_pos),
      lt_of_le_of_lt (min_le_left _ _) (by norm_num), ?_⟩
    have hd : dist (min (1 / 4) (ηd / 2)) 0 < ηd := by
      rw [Real.dist_eq, sub_zero, abs_of_pos (lt_min (by norm_num) (half_pos hηd_pos))]
      exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have h1 := hηd hd
    simp only [Real.dist_eq, sub_zero, one_pow] at h1
    linarith [(abs_lt.mp h1).1]
  -- Choose ball `m_ball` covering `s₁` and all nearby `s_T n, s_B n`.
  let m_ball : ℕ := Nat.ceil (|s₁| + 2)
  have hm_ge : |s₁| + 2 ≤ (m_ball : ℝ) + 1 :=
    (Nat.le_ceil _).trans (by linarith)
  have hdiff_S : Differentiable ℂ (normProfileS airyExtremal) := fun z => by
    unfold normProfileS normProfile
    exact (((differentiable_airyExtremal (-((betaTip : ℝ) : ℂ) * z)).comp z
      ((differentiableAt_id).const_mul (-((betaTip : ℝ) : ℂ)))).const_mul _).const_mul _
  have hcont_derivS : ContinuousAt (deriv (normProfileS airyExtremal)) (s₁ : ℂ) := by
    have h_an : AnalyticOnNhd ℂ (normProfileS airyExtremal) univ :=
      (Complex.analyticOnNhd_univ_iff_differentiable).2 hdiff_S
    exact ((h_an.deriv (s₁ : ℂ) (mem_univ _)).continuousAt)
  have hderiv_val : (deriv (normProfileS airyExtremal) (s₁ : ℂ)).re = slope₀ := by
    have hs1_eq : (s₁ : ℂ) = (((-airyZero 1 / betaTip : ℝ) : ℂ)) := rfl
    rw [hs1_eq, deriv_normProfileS_airyExtremal_at, Complex.ofReal_re]
  obtain ⟨r_ball, hr_pos, hr_ball⟩ := Metric.continuousAt_iff.mp hcont_derivS
    (slope₀ * δ_err / 2) (by positivity)
  let r₀ : ℝ := min 1 r_ball
  have hr₀_pos : 0 < r₀ := lt_min one_pos hr_pos
  have hderiv_unif := Metric.tendstoUniformlyOn_iff.mp (hderiv_lim m_ball)
    (slope₀ * δ_err / 2) (by positivity)
  -- `lemmaQ_general_part2` gives `AnalyticOnNhd` and real-axis sign preservation
  obtain ⟨c₂, C₀, _, _, hpart2⟩ := lemmaQ_general_part2 D
  -- `one_level_clusters` gives attaining measure at `B n` with weight `w₀⁻¹ + o(1)`
  let R_K : ℝ := (|airyZero 1| + |airyZero 2|) / 2
  have h12_lt : airyZero 2 < airyZero 1 := airyZero_lt_of_lt le_rfl (by omega)
  have hRK_lo : |airyZero 1| < R_K := by
    dsimp [R_K]; rw [abs_of_neg (airyZero_neg 1), abs_of_neg (airyZero_neg 2)]; linarith
  have hRK_hi : R_K < |airyZero 2| := by
    dsimp [R_K]; rw [abs_of_neg (airyZero_neg 1), abs_of_neg (airyZero_neg 2)]; linarith
  obtain ⟨tStar, -, -, h_cl_sup, -, h_cl_pos, h_cl_wt, -⟩ :=
    one_level_clusters prob 1 le_rfl hRK_lo hRK_hi hc_tend
  -- Combine all eventual properties at a single index `n`
  have hac_ev : ∀ᶠ n in atTop, M_dom ≤ virasoroAC (c n) ^ 2 := by
    have h1 : Tendsto (fun c : ℝ => virasoroAC c ^ 2) atTop atTop :=
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).const_mul_atTop
        (mul_pos two_pos (pow_pos virasoroBV_pos 2))).congr'
        (by filter_upwards [eventually_ge_atTop (0 : ℝ)] with c hc; rw [virasoroAC_sq c hc])
    exact (h1.comp hc_tend).eventually_ge_atTop M_dom
  have hchart_ac_ev : ∀ᶠ n in atTop, M_dom ≤ chartAC D.r_1 (c n) ^ 2 :=
    ((tendsto_chartAC_sq D.hr1_pos).comp hc_tend).eventually_ge_atTop M_dom
  have hdom_ball_ev : ∀ᶠ n in atTop, M_dom < virasoroRUInf * (c n) ^ ((2 : ℝ) / 3) :=
    (((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp hc_tend).const_mul_atTop
      virasoroRUInf_pos).eventually_gt_atTop M_dom
  have h_all : ∀ᶠ n in atTop,
      c₂ ≤ c n ∧ c_ut ≤ c n ∧
      0 < B n ∧ 0 < T n ∧ |uAiry (c n) (T n)| ≤ M_win ∧ |uAiry (c n) (B n)| ≤ M_win ∧
      M_dom ≤ virasoroAC (c n) ^ 2 ∧ M_dom ≤ chartAC D.r_1 (c n) ^ 2 ∧
      M_dom < virasoroRUInf * (c n) ^ ((2 : ℝ) / 3) ∧
      |s_T n - s₁| < r₀ ∧ |s_B n - s₁| < r₀ ∧
      (∀ s ∈ closedBall (0 : ℂ) ((m_ball : ℝ) + 1),
        dist (deriv (normProfileS airyExtremal) s) (deriv (psiTildeS prob (c n) (g n)) s) < slope₀ * δ_err / 2) ∧
      (∀ u : ℝ, |u| ≤ M_dom → |-deriv (virasoroDeltaChart (c n)) u / (cStar * (c n) ^ ((1 : ℝ) / 3)) - 1| ≤ δ_err) ∧
      |jacRatio (c n) (B n) - 1| ≤ δ_err ∧
      tStar 0 n = B n ∧
      (∀ meas : AdmissibleCrossingMeasure prob (c n / 12), meas.ν (Ici (B n))ᶜ = 0 →
        |spectralWeight prob (c n) (B n) * (meas.ν {B n}).toReal - airyNodeWeight 0| ≤
          airyNodeWeight 0 * δ_err) := by
    filter_upwards [hc_tend.eventually_ge_atTop c₂, hc_tend.eventually_ge_atTop c_ut,
      hTV_ev, hT_pos, huT_bd, huB_bd, hac_ev, hchart_ac_ev, hdom_ball_ev,
      hs_T_tend.eventually (Metric.tendsto_nhds.mp tendsto_id r₀ hr₀_pos),
      hs_B_tend.eventually (Metric.tendsto_nhds.mp tendsto_id r₀ hr₀_pos),
      hderiv_unif,
      hc_tend.eventually (deriv_virasoroDeltaChart_div_tendsto M_dom hM_dom δ_err hδ_pos),
      hc_tend.eventually (jacRatio_tendsto_one M_win hM_win δ_err hδ_pos),
      h_cl_sup,
      h_cl_wt (airyNodeWeight 0 * δ_err) (mul_pos (airyNodeWeight_pos 0) hδ_pos)]
      with n hc2 hcut hBn hTn huT huB hac hcA hru hsT hsB hder_u hder_c hjr hsup hwt
    refine ⟨hc2, hcut, hBn, hTn, huT, huB, hac, hcA, hru, ?_, ?_, hder_u, hder_c,
      hjr (B n) hBn huB, hsup.2.1, ?_⟩
    · rwa [← Real.dist_eq]
    · rwa [← Real.dist_eq]
    · intro meas hm_supp
      have h_w := hwt meas hm_supp 0
      have ht0 : tStar 0 n = B n := hsup.2.1
      rw [ht0] at h_w
      exact h_w
  obtain ⟨n, hc2_n, hcut_n, hBn_pos, hTn_pos, huT_n, huB_n, hac_n, hcA_n, hru_n,
    hsT_ball, hsB_ball, hder_u, hder_c, hjr, _, hwt_n⟩ := h_all.exists
  obtain ⟨huT_mem, hΔ_T, -⟩ := hC_ut hcut_n hTn_pos huT_n
  obtain ⟨huB_mem, hΔ_B, -⟩ := hC_ut hcut_n hBn_pos huB_n
  have huT_vir : |u_T n| ≤ virasoroAC (c n) ^ 2 := huT_mem.trans hac_n
  have huB_vir : |u_B n| ≤ virasoroAC (c n) ^ 2 := huB_mem.trans hac_n
  have huT_cA : |u_T n| ≤ chartAC D.r_1 (c n) ^ 2 := huT_mem.trans hcA_n
  have huB_cA : |u_B n| ≤ chartAC D.r_1 (c n) ^ 2 := huB_mem.trans hcA_n
  -- `u_B n < u_T n` from `T n < B n` and `virasoroDeltaChart_strictAnti`, hence `s_T n < s_B n`.
  have hT_lt_B : T n < B n := by dsimp [T]; linarith [hη_pos n]
  have hu_lt : u_B n < u_T n := by
    by_contra hle; push Not at hle
    have hanti := (virasoroDeltaChart_strictAnti (hc_pos n)).antitoneOn
      (abs_le.mp huT_vir) (abs_le.mp huB_vir) hle
    rw [hΔ_T, hΔ_B] at hanti
    linarith
  have hs_lt : s_T n < s_B n := by
    dsimp [s_T, s_B]; rw [div_lt_div_iff_of_pos_right hb_pos]; linarith
  -- Analyticity & sign at `u_T n` from `lemmaQ_general_part2`
  have hM_n_pos : 0 < prob.cardyNorm (c n / 12) (g n) := by rw [hg_M n]; exact one_pos
  obtain ⟨han_n, hsign_n, -⟩ := hpart2 hc2_n (hg_tc n) hM_n_pos
  have hfT_nn : 0 ≤ (psiTildeS prob (c n) (g n) (s_T n : ℂ)).re := by
    have h1 : -((betaTip : ℝ) : ℂ) * (s_T n : ℂ) = (u_T n : ℂ) := by
      dsimp [s_T]; push_cast; field_simp [hb_pos.ne']
    have hpsi_eq : (psiTildeS prob (c n) (g n) (s_T n : ℂ)).re =
        betaTip * (psiTilde prob (c n) (g n) (u_T n : ℂ)).re := by
      unfold psiTildeS; rw [h1]; simp [Complex.mul_re]
    rw [hpsi_eq]
    have hgt_nn : 0 ≤ g n (virasoroDeltaChart (c n) (u_T n)) := by
      rw [hΔ_T]; exact hg_nn n (T n) le_rfl
    exact mul_nonneg hb_pos.le ((hsign_n (u_T n) huT_cA).2.mp hgt_nn)
  -- Real MVT on `s ↦ (psiTildeS ... (s : ℂ)).re` on `[s_T n, s_B n]`
  let fS : ℝ → ℝ := fun s => (psiTildeS prob (c n) (g n) (s : ℂ)).re
  have hu_seg : ∀ s ∈ Icc (s_T n) (s_B n), |-betaTip * s| ≤ M_dom := fun s hs => by
    have hsb_eq : -betaTip * s_B n = u_B n := by dsimp [s_B]; field_simp [hb_pos.ne']
    have hst_eq : -betaTip * s_T n = u_T n := by dsimp [s_T]; field_simp [hb_pos.ne']
    have hm1 := mul_le_mul_of_nonneg_left hs.1 hb_pos.le
    have hm2 := mul_le_mul_of_nonneg_left hs.2 hb_pos.le
    have h1 : u_B n ≤ -betaTip * s := by linarith
    have h2 : -betaTip * s ≤ u_T n := by linarith
    exact abs_le.mpr ⟨by linarith [(abs_le.mp huB_mem).1], by linarith [(abs_le.mp huT_mem).2]⟩
  have hderiv_fS : ∀ s ∈ Icc (s_T n) (s_B n),
      HasDerivAt fS ((deriv (psiTildeS prob (c n) (g n)) (s : ℂ)).re) s ∧
      slope₀ * (1 - δ_err) ≤ (deriv (psiTildeS prob (c n) (g n)) (s : ℂ)).re := by
    intro s hs
    have h_uabs : |-betaTip * s| ≤ M_dom := hu_seg s hs
    have h_uvir : |-betaTip * s| ≤ virasoroAC (c n) ^ 2 := h_uabs.trans hac_n
    have h_udom : ((-betaTip * s : ℝ) : ℂ) ∈ psiDom (c n) := by
      refine ⟨?_, ?_⟩
      · rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]
        exact lt_of_le_of_lt h_uabs hru_n
      · have hb_real := virasoroBChart_ofReal (hc_pos n) h_uvir
        rw [hb_real.1, abs_zero]; norm_num
    have h_an_u : AnalyticAt ℂ (psiTilde prob (c n) (g n)) (-((betaTip : ℝ) : ℂ) * (s : ℂ)) :=
      han_n _ (by simpa only [Complex.ofReal_mul, Complex.ofReal_neg] using h_udom)
    have h_diff_S : DifferentiableAt ℂ (psiTildeS prob (c n) (g n)) (s : ℂ) := by
      show DifferentiableAt ℂ (fun z : ℂ => ((betaTip : ℝ) : ℂ) *
        psiTilde prob (c n) (g n) (-((betaTip : ℝ) : ℂ) * z)) (s : ℂ)
      exact (h_an_u.differentiableAt.comp (s : ℂ)
        ((differentiableAt_id).const_mul (-((betaTip : ℝ) : ℂ)))).const_mul _
    have hd_re : HasDerivAt fS ((deriv (psiTildeS prob (c n) (g n)) (s : ℂ)).re) s := by
      have hc_deriv := h_diff_S.hasDerivAt.comp_ofReal
      exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt s hc_deriv
    have hs_s1 : |s - s₁| < r₀ := by
      have ha1 := abs_lt.mp hsT_ball
      have ha2 := abs_lt.mp hsB_ball
      exact abs_lt.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hs_ball : (s : ℂ) ∈ closedBall (0 : ℂ) ((m_ball : ℝ) + 1) := by
      rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]
      have : |s| ≤ |s₁| + 1 := by
        have := hs_s1.trans_le (min_le_left _ _)
        linarith [abs_sub_abs_le_abs_sub s s₁]
      linarith
    have h1 := hr_ball (show dist (s : ℂ) (s₁ : ℂ) < r_ball by
      rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      exact hs_s1.trans_le (min_le_right _ _))
    have h2 := hder_u (s : ℂ) hs_ball
    have h_norm_sub : ‖deriv (psiTildeS prob (c n) (g n)) (s : ℂ) - ((slope₀ : ℝ) : ℂ)‖ <
        slope₀ * δ_err := by
      rw [← Complex.dist_eq]
      have heq_sl : deriv (normProfileS airyExtremal) (s₁ : ℂ) = ((slope₀ : ℝ) : ℂ) := by
        have hs1_eq : (s₁ : ℂ) = (((-airyZero 1 / betaTip : ℝ) : ℂ)) := rfl
        rw [hs1_eq, deriv_normProfileS_airyExtremal_at]
      rw [heq_sl] at h1
      calc dist (deriv (psiTildeS prob (c n) (g n)) (s : ℂ)) ((slope₀ : ℝ) : ℂ)
          ≤ dist (deriv (psiTildeS prob (c n) (g n)) (s : ℂ)) (deriv (normProfileS airyExtremal) (s : ℂ)) +
            dist (deriv (normProfileS airyExtremal) (s : ℂ)) ((slope₀ : ℝ) : ℂ) := dist_triangle _ _ _
        _ = dist (deriv (normProfileS airyExtremal) (s : ℂ)) (deriv (psiTildeS prob (c n) (g n)) (s : ℂ)) +
            dist (deriv (normProfileS airyExtremal) (s : ℂ)) ((slope₀ : ℝ) : ℂ) := by rw [dist_comm]
        _ < slope₀ * δ_err / 2 + slope₀ * δ_err / 2 := add_lt_add h2 h1
        _ = slope₀ * δ_err := by ring
    have h_re_diff : |(deriv (psiTildeS prob (c n) (g n)) (s : ℂ)).re - slope₀| < slope₀ * δ_err := by
      have : (deriv (psiTildeS prob (c n) (g n)) (s : ℂ)).re - slope₀ =
          ((deriv (psiTildeS prob (c n) (g n)) (s : ℂ) - ((slope₀ : ℝ) : ℂ)).re) := by
        simp only [Complex.sub_re, Complex.ofReal_re]
      rw [this]; exact (abs_re_le_norm _).trans_lt h_norm_sub
    exact ⟨hd_re, by linarith [(abs_lt.mp h_re_diff).1]⟩
  have hmvt_S : slope₀ * (1 - δ_err) * (s_B n - s_T n) ≤ fS (s_B n) - fS (s_T n) := by
    have hcont : ContinuousOn fS (Icc (s_T n) (s_B n)) := fun s hs =>
      (hderiv_fS s hs).1.continuousAt.continuousWithinAt
    obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope fS _ hs_lt hcont
      fun s hs => (hderiv_fS s (Ioo_subset_Icc_self hs)).1
    have h_deriv_lb := (hderiv_fS ξ (Ioo_subset_Icc_self hξ)).2
    have hne : s_B n - s_T n ≠ 0 := (sub_pos.mpr hs_lt).ne'
    rw [eq_div_iff hne] at hslope
    rw [← hslope]
    exact mul_le_mul_of_nonneg_right h_deriv_lb (sub_pos.mpr hs_lt).le
  -- Real MVT on `virasoroDeltaChart (c n)` on `[u_B n, u_T n]`
  have hmvt_Δ : η n ≤ (1 + δ_err) * cStar * (c n) ^ ((1 : ℝ) / 3) * (u_T n - u_B n) := by
    have hderiv_Δ : ∀ u ∈ Icc (u_B n) (u_T n),
        HasDerivAt (virasoroDeltaChart (c n)) (deriv (virasoroDeltaChart (c n)) u) u ∧
        -deriv (virasoroDeltaChart (c n)) u ≤ (1 + δ_err) * cStar * (c n) ^ ((1 : ℝ) / 3) := by
      intro u hu
      have hu_dom : |u| ≤ M_dom := abs_le.mpr
        ⟨by linarith [(abs_le.mp huB_mem).1, hu.1], by linarith [(abs_le.mp huT_mem).2, hu.2]⟩
      have hd := virasoroDeltaChart_hasDerivAt (hc_pos n) (hu_dom.trans hac_n)
      have hcS_pos : 0 < cStar * (c n) ^ ((1 : ℝ) / 3) :=
        mul_pos cStar_pos (Real.rpow_pos_of_pos (hc_pos n) _)
      have h_bd : -deriv (virasoroDeltaChart (c n)) u / (cStar * (c n) ^ ((1 : ℝ) / 3)) ≤ 1 + δ_err := by
        linarith [(abs_le.mp (hder_c u hu_dom)).2]
      rw [div_le_iff₀ hcS_pos] at h_bd
      exact ⟨hd.deriv ▸ hd, by linarith⟩
    have hcont_Δ : ContinuousOn (virasoroDeltaChart (c n)) (Icc (u_B n) (u_T n)) := fun u hu =>
      (hderiv_Δ u hu).1.continuousAt.continuousWithinAt
    obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope (virasoroDeltaChart (c n)) _ hu_lt hcont_Δ
      fun u hu => (hderiv_Δ u (Ioo_subset_Icc_self hu)).1
    have hne : u_T n - u_B n ≠ 0 := (sub_pos.mpr hu_lt).ne'
    rw [eq_div_iff hne, hΔ_T, hΔ_B] at hslope
    have hη_eq : η n = (-deriv (virasoroDeltaChart (c n)) ξ) * (u_T n - u_B n) := by
      have hTB : T n = B n - η n := rfl
      linarith only [hTB, hslope]
    rw [hη_eq]
    exact mul_le_mul_of_nonneg_right (hderiv_Δ ξ (Ioo_subset_Icc_self hξ)).2 (sub_pos.mpr hu_lt).le
  -- Lower bound on `(psiTilde prob (c n) (g n) (u_B n : ℂ)).re`
  have hpsi_B_lb : w₀ * kappaRes * (1 - δ_err) ^ 2 * (c n) ^ (-(1 / 3 : ℝ)) * η n ≤
      (psiTilde prob (c n) (g n) (u_B n : ℂ)).re := by
    have hs_eq_u : s_B n - s_T n = (u_T n - u_B n) / betaTip := by
      dsimp [s_B, s_T]; ring
    have hfB_eq : fS (s_B n) = betaTip * (psiTilde prob (c n) (g n) (u_B n : ℂ)).re := by
      have h1 : -((betaTip : ℝ) : ℂ) * (s_B n : ℂ) = (u_B n : ℂ) := by
        dsimp [s_B]; push_cast; field_simp [hb_pos.ne']
      dsimp [fS]; unfold psiTildeS; rw [h1]; simp [Complex.mul_re]
    have h1p : 0 < 1 + δ_err := by linarith only [hδ_pos]
    have hinv_le : (1 - δ_err) ≤ (1 + δ_err)⁻¹ := by
      rw [← one_div, le_div_iff₀ h1p]
      nlinarith only [sq_nonneg δ_err]
    have hcS_pos : 0 < cStar * (c n) ^ ((1 : ℝ) / 3) :=
      mul_pos cStar_pos (Real.rpow_pos_of_pos (hc_pos n) _)
    have hu_diff_lb : (1 - δ_err) * η n / (cStar * (c n) ^ ((1 : ℝ) / 3)) ≤ u_T n - u_B n := by
      have h1 : η n / ((1 + δ_err) * cStar * (c n) ^ ((1 : ℝ) / 3)) ≤ u_T n - u_B n := by
        rw [div_le_iff₀ (mul_pos (mul_pos h1p cStar_pos) (Real.rpow_pos_of_pos (hc_pos n) _))]
        calc η n ≤ (1 + δ_err) * cStar * (c n) ^ ((1 : ℝ) / 3) * (u_T n - u_B n) := hmvt_Δ
          _ = (u_T n - u_B n) * ((1 + δ_err) * cStar * (c n) ^ ((1 : ℝ) / 3)) := by ring
      calc (1 - δ_err) * η n / (cStar * (c n) ^ ((1 : ℝ) / 3))
          ≤ (1 + δ_err)⁻¹ * η n / (cStar * (c n) ^ ((1 : ℝ) / 3)) := by
            exact div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_right hinv_le (hη_pos n).le) hcS_pos.le
        _ = η n / ((1 + δ_err) * cStar * (c n) ^ ((1 : ℝ) / 3)) := by
            field_simp [h1p.ne', hcS_pos.ne']
        _ ≤ u_T n - u_B n := h1
    have h1 : slope₀ * (1 - δ_err) * ((u_T n - u_B n) / betaTip) ≤
        betaTip * (psiTilde prob (c n) (g n) (u_B n : ℂ)).re := by
      rw [← hs_eq_u, ← hfB_eq]
      linarith only [hmvt_S, hfT_nn]
    have h2 : (w₀ / (2 * LStar)) * (1 - δ_err) * (u_T n - u_B n) ≤
        (psiTilde prob (c n) (g n) (u_B n : ℂ)).re := by
      have h_mul := mul_le_mul_of_nonneg_left h1 (inv_pos.mpr hb_pos).le
      have h_id1 : betaTip⁻¹ * (slope₀ * (1 - δ_err) * ((u_T n - u_B n) / betaTip)) =
          (w₀ / (2 * LStar)) * (1 - δ_err) * (u_T n - u_B n) := by
        dsimp [slope₀]; field_simp [hb_pos.ne', LStar_pos.ne']
      have h_id2 : betaTip⁻¹ * (betaTip * (psiTilde prob (c n) (g n) (u_B n : ℂ)).re) =
          (psiTilde prob (c n) (g n) (u_B n : ℂ)).re := by
        field_simp [hb_pos.ne']
      rwa [h_id1, h_id2] at h_mul
    calc w₀ * kappaRes * (1 - δ_err) ^ 2 * (c n) ^ (-(1 / 3 : ℝ)) * η n
        = (w₀ / (2 * LStar)) * (1 - δ_err) * ((1 - δ_err) * η n / (cStar * (c n) ^ ((1 : ℝ) / 3))) := by
          have hc_neg : (c n) ^ (-(1 / 3 : ℝ)) = ((c n) ^ ((1 : ℝ) / 3))⁻¹ := by
            rw [Real.rpow_neg (hc_pos n).le, one_div]
          unfold kappaRes; rw [hc_neg]; field_simp [cStar_pos.ne', LStar_pos.ne',
            (Real.rpow_pos_of_pos (hc_pos n) _).ne']
      _ ≤ (w₀ / (2 * LStar)) * (1 - δ_err) * (u_T n - u_B n) := by
          have hwL_nn : 0 ≤ (w₀ / (2 * LStar)) * (1 - δ_err) :=
            mul_nonneg (div_nonneg hw₀_pos.le (mul_pos two_pos LStar_pos).le) (by linarith [hδ_lt_half])
          exact mul_le_mul_of_nonneg_left hu_diff_lb hwL_nn
      _ ≤ (psiTilde prob (c n) (g n) (u_B n : ℂ)).re := h2
  -- Pair `g n` with optimal crossing measure `meas` at gap `B n`
  obtain ⟨meas, hmeas_lo, -, -⟩ := corollary_E1_exact_gap prob (hc_pos n) (hshift_n n) hBn_pos
  have hmeas_supp : meas.ν (Ici (B n))ᶜ = 0 := by
    rw [show (Ici (B n))ᶜ = Iio (B n) by ext t; simp]; exact hmeas_lo
  have ha_n : prob.totalShift ≤ c n / 12 := by linarith [hshift_n n]
  have ha0_n : 0 < c n / 12 := by linarith [hc_pos n]
  obtain ⟨hint_ν, hfw⟩ := lemma_fwX_one_sided_unconditional prob ha_n ha0_n meas (hg_tc n)
    (T := B n) (fun t ht => hg_nn n t (by linarith [show B n = prob.T_V (c n) from rfl, hη_pos n]))
  have h_pair_lb : g n (B n) * (meas.ν {B n}).toReal / (2 * Real.pi) ≤ slack n := by
    have h_mono : ∫ t in ({B n} : Set ℝ), g n t ∂meas.ν ≤ ∫ t in Ici (0 : ℝ), g n t ∂meas.ν := by
      rw [Duality.restrict_Ici_eq_self meas]
      have h_res : IntegrableOn (g n) (univ : Set ℝ) meas.ν := by
        rw [IntegrableOn, Measure.restrict_univ]
        rwa [IntegrableOn, Duality.restrict_Ici_eq_self meas] at hint_ν
      have h_ae_univ : ∀ᵐ t ∂meas.ν, 0 ≤ g n t := by
        filter_upwards [ae_mem_of_null hmeas_supp] with t ht
        exact hg_nn n t (by linarith [show B n = prob.T_V (c n) from rfl, hη_pos n, show B n ≤ t from ht])
      rw [← setIntegral_univ (f := g n) (μ := meas.ν)]
      exact setIntegral_mono_set h_res (ae_restrict_of_ae h_ae_univ)
        (Eventually.of_forall fun _ _ => mem_univ _)
    have h_atom : ∫ t in ({B n} : Set ℝ), g n t ∂meas.ν = g n (B n) * (meas.ν {B n}).toReal := by
      rw [Measure.restrict_singleton, integral_smul_measure, integral_dirac, smul_eq_mul, mul_comm]
    have hgvac : -prob.gVac (c n / 12) (g n) = 2 * Real.pi * slack n := by
      dsimp [slack]; unfold FixedWeightProblem.gVac; ring
    have h1 : g n (B n) * (meas.ν {B n}).toReal ≤ 2 * Real.pi * slack n := by
      linarith [hfw, h_mono, h_atom, hgvac]
    rwa [div_le_iff₀ (mul_pos two_pos Real.pi_pos), mul_comm (slack n)]
  -- Express `g n (B n) / (2π) * meas.ν {B n}` via `jacRatio * spectralWeight * psiTilde`
  have h_prod_eq : g n (B n) * (meas.ν {B n}).toReal / (2 * Real.pi) =
      jacRatio (c n) (B n) * (spectralWeight prob (c n) (B n) * (meas.ν {B n}).toReal) *
        (psiTilde prob (c n) (g n) (u_B n : ℂ)).re := by
    have hgs := gs_div_two_pi_eq_jacRatio prob (hc_pos n) ha_n hBn_pos (hg_tc n) (hg_M n) huB_vir hΔ_B
    calc g n (B n) * (meas.ν {B n}).toReal / (2 * Real.pi)
        = (g n (B n) / (2 * Real.pi)) * (meas.ν {B n}).toReal := by ring
      _ = (jacRatio (c n) (B n) * spectralWeight prob (c n) (B n) *
            (psiTilde prob (c n) (g n) (u_B n : ℂ)).re) * (meas.ν {B n}).toReal := by rw [hgs]
      _ = _ := by ring
  have hjr_lb : 1 - δ_err ≤ jacRatio (c n) (B n) := by linarith [(abs_le.mp hjr).1]
  have hwt_lb : airyNodeWeight 0 * (1 - δ_err) ≤
      spectralWeight prob (c n) (B n) * (meas.ν {B n}).toReal := by
    linarith [(abs_le.mp (hwt_n meas hmeas_supp)).1]
  have hw0_eq : airyNodeWeight 0 = w₀⁻¹ := by
    unfold airyNodeWeight airyNode; dsimp [w₀]; simp
  have h_final_lb : (1 - δ_err) ^ 4 * kappaRes * (c n) ^ (-(1 / 3 : ℝ)) * η n ≤ slack n := by
    have hjr_nn : 0 ≤ 1 - δ_err := by linarith [hδ_lt_half]
    have hwt_nn : 0 ≤ airyNodeWeight 0 * (1 - δ_err) := mul_nonneg (airyNodeWeight_pos 0).le hjr_nn
    have hpsi_nn : 0 ≤ w₀ * kappaRes * (1 - δ_err) ^ 2 * (c n) ^ (-(1 / 3 : ℝ)) * η n := by
      have := kappaRes_pos; have := (hc_pos n).le; have := (hη_pos n).le; positivity
    have hjr_nn2 : 0 ≤ jacRatio (c n) (B n) := hjr_nn.trans hjr_lb
    have hjr_prod_nn :
        0 ≤ jacRatio (c n) (B n) * (spectralWeight prob (c n) (B n) * (meas.ν {B n}).toReal) :=
      mul_nonneg hjr_nn2 (hwt_nn.trans hwt_lb)
    calc (1 - δ_err) ^ 4 * kappaRes * (c n) ^ (-(1 / 3 : ℝ)) * η n
        = (1 - δ_err) * (airyNodeWeight 0 * (1 - δ_err)) *
            (w₀ * kappaRes * (1 - δ_err) ^ 2 * (c n) ^ (-(1 / 3 : ℝ)) * η n) := by
          rw [hw0_eq]; field_simp [hw₀_pos.ne']
      _ ≤ jacRatio (c n) (B n) * (spectralWeight prob (c n) (B n) * (meas.ν {B n}).toReal) *
            (psiTilde prob (c n) (g n) (u_B n : ℂ)).re :=
          mul_le_mul (mul_le_mul hjr_lb hwt_lb hwt_nn hjr_nn2) hpsi_B_lb hpsi_nn hjr_prod_nn
      _ = g n (B n) * (meas.ν {B n}).toReal / (2 * Real.pi) := h_prod_eq.symm
      _ ≤ slack n := h_pair_lb
  have h_pos_fac : 0 < kappaRes * (c n) ^ (-(1 / 3 : ℝ)) * η n :=
    mul_pos (mul_pos kappaRes_pos (Real.rpow_pos_of_pos (hc_pos n) _)) (hη_pos n)
  have h_lt_contra : (1 - ε) * kappaRes * (c n) ^ (-(1 / 3 : ℝ)) * η n <
      (1 - δ_err) ^ 4 * kappaRes * (c n) ^ (-(1 / 3 : ℝ)) * η n := by
    have h := mul_lt_mul_of_pos_right hδ_pow4 h_pos_fac
    linarith
  linarith [hslack_lt n, h_final_lb, h_lt_contra]

/-- Convenience form of `int_reserve_lower_testClass` as a normalized ratio lower bound for `H ≡ 1`. -/
theorem int_reserve_lower_const (prob : FixedWeightProblem) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ c₀ : ℝ, max 1 (12 * prob.totalShift) ≤ c₀ ∧
      ∀ {c η : ℝ}, c₀ ≤ c → 0 < η → η ≤ 1 →
        ∀ {g : ℝ → ℝ}, TestClass prob (c / 12) g → (∃ t ≥ 0, g t ≠ 0) →
          (∀ t : ℝ, prob.T_V c - η ≤ t → 0 ≤ g t) →
          (1 - ε) * kappaRes * c ^ (-(1 / 3 : ℝ)) * η ≤
            (∫ t in Ioi (0 : ℝ), g t * prob.cardyV (c / 12) t) / prob.cardyNorm (c / 12) g := by
  have hHo : (fun _ : ℝ => (1 : ℝ)) =o[atTop] fun c : ℝ => c ^ ((1 : ℝ) / 3) := by
    refine Asymptotics.isLittleO_of_tendsto' ?_ ?_
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc h0
      exact absurd h0 (Real.rpow_pos_of_pos hc _).ne'
    · simpa using tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)
        |>.congr' (by filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
                      rw [Real.rpow_neg hc.le, one_div])
  obtain ⟨c₀, hc₀, hbound⟩ := int_reserve_lower_testClass prob hε0 hε1 hHo
  refine ⟨c₀, hc₀, fun {c η} hc hη0 hη1 {g} hg hne hnn => ?_⟩
  have hc_pos : 0 < c := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans (hc₀.trans hc))
  have hsh : prob.totalShift ≤ c / 12 := by
    have := (le_max_right 1 (12 * prob.totalShift)).trans (hc₀.trans hc); linarith
  have hM := cardyNorm_pos_of_nonzero_general prob hsh hg hne
  exact (le_div_iff₀ hM).mpr (hbound hc hη0 hη1 hg hne hnn)

end FormalResearch.ModularBootstrap.Integrality

/-- info: 'FormalResearch.ModularBootstrap.Integrality.int_reserve_lower_testClass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Integrality.int_reserve_lower_testClass

/-- info: 'FormalResearch.ModularBootstrap.Integrality.int_reserve_lower_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Integrality.int_reserve_lower_const
