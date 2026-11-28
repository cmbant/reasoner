module

public import FormalResearch.SignUncertainty.CtBoasHarmonicBounds

/-!
# `ct:boas` Steps 3–5: exact-phase harmonic estimate (`O(c^{-14})`) on every near block

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, `ct:boas` Steps 3–5.
For `c ≥ c₀`, `ε = ±1`, `c₁² c^{2/3} ≤ R ≤ 4 c₁² c^{2/3}`, `j < N`, and `2 ≤ k ≤ ⌈c²⌉`:

`boas_harmonic_bound`:
`|∫ nearWeight ε c R j L * hankelHL c f L * cos (k * (boasX c ε L + π/2)) dL| ≤ C_har * M[f] * c^{-14}`.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.SignUncertainty.FctSym

/-- **Exact-phase harmonic estimate** (`ct:boas` Steps 3–5): for `c₁ ∈ (0, c₁₀]` and `c ≥ c₀`,
for every near block `j < N` and harmonic `2 ≤ k ≤ ⌈c²⌉`,
`|∫ nearWeight ε c R j L * hankelHL c f L * cos (k * (boasX c ε L + π/2)) dL| ≤ C_har M[f] c^{-14}`. -/
theorem boas_harmonic_bound : ∃ c₁₀ : ℝ, 0 < c₁₀ ∧
    ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ c₁₀ → ∃ c₀ C_har : ℝ, Real.exp 2 ≤ c₀ ∧ 0 ≤ C_har ∧
      ∀ {ε c R : ℝ} {f : ℝ → ℝ},
        (ε = 1 ∨ ε = -1) → c₀ ≤ c →
        c₁ ^ 2 * c ^ (2 / 3 : ℝ) ≤ R → R ≤ 4 * c₁ ^ 2 * c ^ (2 / 3 : ℝ) →
        IsHankelEigenfn c ε f →
        ∀ j ∈ Finset.range (partCount (ctLv0 c / 4) (nearB c)),
          ∀ k : ℕ, 2 ≤ k → k ≤ Nat.ceil (c ^ 2) →
            |∫ L : ℝ, nearWeight ε c R j L * hankelHL c f L * Real.cos ((k : ℝ) * (boasX c ε L + π / 2))| ≤
              C_har * hankelMass c f * c ^ (-(14 : ℝ)) := by
  obtain ⟨c₁₀, hc₁₀, hnw⟩ := exists_near_weights
  obtain ⟨c_x, hcx3, hx_drv, hx_sym⟩ := boasX_deriv_and_symbol
  obtain ⟨κ_L, hκL_pos, cL, hcL1, hLv0⟩ := ctLv0_facts
  choose C_X hCX_nn hx_sym using hx_sym
  let CX2 : ℝ := C_X 2 (by norm_num)
  let Bθ : ℕ → ℝ := fun i => (1.1 / 0.015) * C_X (i + 1) (Nat.succ_pos i)
  have hBθ0 : ∀ i, 0 ≤ Bθ i := fun i => by dsimp only [Bθ]; exact mul_nonneg (by positivity) (hCX_nn _ _)
  obtain ⟨C_D, hCD0, hibp_r⟩ := osc_ibp_r 200 Bθ hBθ0
  refine ⟨c₁₀, hc₁₀, fun c₁ hc₁ hle => ?_⟩
  obtain ⟨c_w, κ_min, hcw_e2, hκmin_pos, C_m, hCm0, hblocks⟩ := hnw c₁ hc₁ hle
  obtain ⟨M_tot_w, hMtotw_eq⟩ :
      ∃ M : ℝ, M = ∑ m' ∈ Finset.range 201, ∑ i ∈ Finset.range (m' + 1), (m'.choose i : ℝ) * C_m i := ⟨_, rfl⟩
  obtain ⟨M_tot_2, hMtot2_eq⟩ :
      ∃ M : ℝ, M = ∑ m' ∈ Finset.range 3, ∑ i ∈ Finset.range (m' + 1), (m'.choose i : ℝ) * C_m i := ⟨_, rfl⟩
  have hMtotw_nn : 0 ≤ M_tot_w := by
    rw [hMtotw_eq]
    exact Finset.sum_nonneg fun m' _ => Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (hCm0 i)
  have hMtot2_nn : 0 ≤ M_tot_2 := by
    rw [hMtot2_eq]
    exact Finset.sum_nonneg fun m' _ => Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (hCm0 i)
  have hev_lam : ∀ᶠ c : ℝ in atTop, max 1 ((ctLv0 c / 4)⁻¹) ≤ c ^ (5 / 6 : ℝ) := by
    have ht := tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 31 / 42)
    have hlim : Tendsto (fun c : ℝ => (5 / κ_L) * c ^ (-(31 / 42 : ℝ))) atTop (𝓝 0) := by
      simpa using ht.const_mul (5 / κ_L)
    filter_upwards [eventually_ge_atTop (max 1 cL), hlim.eventually (Iic_mem_nhds one_pos)] with c hc1 hc_lam
    have hc_pos : 0 < c := lt_of_lt_of_le one_pos (le_trans (le_max_left _ _) hc1)
    have hc_L : cL ≤ c := le_trans (le_max_right _ _) hc1
    obtain ⟨hL0, _, _, hL_lb⟩ := hLv0 c hc_L
    have hc56 : 1 ≤ c ^ (5 / 6 : ℝ) := Real.one_le_rpow (le_trans (le_max_left _ _) hc1) (by norm_num)
    refine max_le hc56 ?_
    rw [inv_div, div_le_iff₀ hL0]
    have h56 : c ^ (5 / 6 : ℝ) * c ^ (-(2 / 21 : ℝ)) = c ^ (31 / 42 : ℝ) := by
      rw [← Real.rpow_add hc_pos]; norm_num
    have hpow_le : 5 / κ_L ≤ c ^ (31 / 42 : ℝ) := by
      calc 5 / κ_L = (5 / κ_L * c ^ (-(31 / 42 : ℝ))) * c ^ (31 / 42 : ℝ) := by
            rw [mul_assoc, ← Real.rpow_add hc_pos]; norm_num
        _ ≤ 1 * c ^ (31 / 42 : ℝ) := mul_le_mul_of_nonneg_right hc_lam (Real.rpow_nonneg hc_pos.le _)
        _ = c ^ (31 / 42 : ℝ) := one_mul _
    have hL_ge : (6 / 5 : ℝ) * κ_L * c ^ (-(2 / 21 : ℝ)) ≤ ctLv0 c := by linarith only [hL_lb]
    calc 4 ≤ (6 / 5 : ℝ) * 5 := by norm_num
      _ ≤ (6 / 5 : ℝ) * κ_L * c ^ (31 / 42 : ℝ) := by
          rw [div_le_iff₀ hκL_pos] at hpow_le; nlinarith only [hpow_le]
      _ = c ^ (5 / 6 : ℝ) * ((6 / 5 : ℝ) * κ_L * c ^ (-(2 / 21 : ℝ))) := by rw [← h56]; ring
      _ ≤ c ^ (5 / 6 : ℝ) * ctLv0 c := mul_le_mul_of_nonneg_left hL_ge (Real.rpow_nonneg hc_pos.le _)
  have hev_cs : ∀ᶠ c : ℝ in atTop, 325 * Real.log c / (κ_min * c ^ (-(2 / 21 : ℝ))) ≤ c ^ (5 / 6 : ℝ) := by
    have h1 := isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 31 / 42)
    have hlim : Tendsto (fun c : ℝ => (325 / κ_min) * (Real.log c / c ^ (31 / 42 : ℝ))) atTop (𝓝 0) := by
      simpa using h1.tendsto_div_nhds_zero.const_mul (325 / κ_min)
    filter_upwards [eventually_gt_atTop (1 : ℝ), hlim.eventually (Iic_mem_nhds one_pos)] with c hc1 hc_s
    have hc0 : 0 < c := zero_lt_one.trans hc1
    have hdiv : 325 / κ_min * Real.log c ≤ c ^ (31 / 42 : ℝ) := by
      calc 325 / κ_min * Real.log c = 325 / κ_min * (Real.log c / c ^ (31 / 42 : ℝ)) * c ^ (31 / 42 : ℝ) := by
            field_simp [(Real.rpow_pos_of_pos hc0 _).ne']
        _ ≤ 1 * c ^ (31 / 42 : ℝ) := mul_le_mul_of_nonneg_right hc_s (Real.rpow_nonneg hc0.le _)
        _ = _ := one_mul _
    have h56 : c ^ (-(2 / 21 : ℝ)) * c ^ (5 / 6 : ℝ) = c ^ (31 / 42 : ℝ) := by
      rw [← Real.rpow_add hc0]; norm_num
    rw [div_le_iff₀ (mul_pos hκmin_pos (Real.rpow_pos_of_pos hc0 _))]
    calc 325 * Real.log c = κ_min * (325 / κ_min * Real.log c) := by field_simp [hκmin_pos.ne']
      _ ≤ κ_min * c ^ (31 / 42 : ℝ) := mul_le_mul_of_nonneg_left hdiv hκmin_pos.le
      _ = c ^ (5 / 6 : ℝ) * (κ_min * c ^ (-(2 / 21 : ℝ))) := by rw [← h56]; ring
  have hev_vert : ∀ᶠ c : ℝ in atTop,
      50 * Real.log c ≤ (1 / 26 : ℝ) * κ_min ^ 2 * c ^ (6 / 7 : ℝ) ∧
      50 * Real.log c ≤ (1 / 26 : ℝ) * κ_min * c ^ (19 / 21 : ℝ) := by
    have h1 := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 6 / 7)).tendsto_div_nhds_zero.const_mul
      (50 * 26 / κ_min ^ 2)
    have h2 := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 19 / 21)).tendsto_div_nhds_zero.const_mul
      (50 * 26 / κ_min)
    filter_upwards [eventually_gt_atTop (1 : ℝ),
      h1.eventually (Iic_mem_nhds (by rw [mul_zero]; exact one_pos)),
      h2.eventually (Iic_mem_nhds (by rw [mul_zero]; exact one_pos))] with c hc1 ha hb
    have hc0 : 0 < c := zero_lt_one.trans hc1
    refine ⟨?_, ?_⟩
    · have hha : 50 * 26 / κ_min ^ 2 * Real.log c ≤ c ^ (6 / 7 : ℝ) := by
        calc 50 * 26 / κ_min ^ 2 * Real.log c = 50 * 26 / κ_min ^ 2 * (Real.log c / c ^ (6 / 7 : ℝ)) * c ^ (6 / 7 : ℝ) := by
              field_simp [(Real.rpow_pos_of_pos hc0 _).ne']
          _ ≤ 1 * c ^ (6 / 7 : ℝ) := mul_le_mul_of_nonneg_right ha (Real.rpow_nonneg hc0.le _)
          _ = _ := one_mul _
      calc 50 * Real.log c = (1 / 26 : ℝ) * κ_min ^ 2 * (50 * 26 / κ_min ^ 2 * Real.log c) := by
            field_simp [hκmin_pos.ne']
        _ ≤ (1 / 26 : ℝ) * κ_min ^ 2 * c ^ (6 / 7 : ℝ) := mul_le_mul_of_nonneg_left hha (by positivity)
    · have hhb : 50 * 26 / κ_min * Real.log c ≤ c ^ (19 / 21 : ℝ) := by
        calc 50 * 26 / κ_min * Real.log c = 50 * 26 / κ_min * (Real.log c / c ^ (19 / 21 : ℝ)) * c ^ (19 / 21 : ℝ) := by
              field_simp [(Real.rpow_pos_of_pos hc0 _).ne']
          _ ≤ 1 * c ^ (19 / 21 : ℝ) := mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hc0.le _)
          _ = _ := one_mul _
      calc 50 * Real.log c = (1 / 26 : ℝ) * κ_min * (50 * 26 / κ_min * Real.log c) := by
            field_simp [hκmin_pos.ne']
        _ ≤ (1 / 26 : ℝ) * κ_min * c ^ (19 / 21 : ℝ) := mul_le_mul_of_nonneg_left hhb (by positivity)
  have hev_tau : ∀ᶠ c : ℝ in atTop, Real.exp (nearB c + 4) ≤ c := by
    have hlog : ∀ᶠ c : ℝ in atTop, π ^ 2 * Real.log c * Real.exp 6 ≤ c := by
      have ht := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero.const_mul
        (π ^ 2 * Real.exp 6)
      filter_upwards [eventually_gt_atTop (1 : ℝ),
        ht.eventually (Iic_mem_nhds (by rw [mul_zero]; exact one_pos))] with c hc1 h
      have hc0 : 0 < c := zero_lt_one.trans hc1
      calc π ^ 2 * Real.log c * Real.exp 6
          = π ^ 2 * Real.exp 6 * (Real.log c / c ^ (1 : ℝ)) * c := by
            rw [Real.rpow_one]; field_simp [hc0.ne']
        _ ≤ 1 * c := mul_le_mul_of_nonneg_right h hc0.le
        _ = c := one_mul _
    filter_upwards [eventually_ge_atTop (Real.exp 2), hlog] with c hce2 hl
    have hc0 : 0 < c := lt_of_lt_of_le (Real.exp_pos 2) hce2
    have hlog2 : 2 ≤ Real.log c := (Real.le_log_iff_exp_le hc0).2 hce2
    have hne : 0 < π ^ 2 * Real.log c := by positivity
    unfold nearB
    calc Real.exp (Real.log (π ^ 2 * Real.log c) + 2 + 4)
        = Real.exp (Real.log (π ^ 2 * Real.log c)) * Real.exp 6 := by rw [← Real.exp_add]; ring_nf
      _ = π ^ 2 * Real.log c * Real.exp 6 := by rw [Real.exp_log hne]
      _ ≤ c := hl
  have hev_deg : ∀ᶠ c : ℝ in atTop, (0.03 * κ_min)⁻¹ ^ 200 ≤ c := eventually_ge_atTop _
  obtain ⟨c₀, hc₀_prop⟩ := ((eventually_ge_atTop (max c_w (max c_x (max cL (Real.exp 2))))).and
    (hev_lam.and (hev_cs.and (hev_vert.and (hev_tau.and hev_deg))))).exists_forall_of_atTop
  have hc₀_ge_e2 : Real.exp 2 ≤ c₀ :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (hc₀_prop c₀ le_rfl).1))
  let C_v2 : ℝ := M_tot_2 * (16 + 3 * CX2)
  have hCv2_nn : 0 ≤ C_v2 := mul_nonneg hMtot2_nn (by have := hCX_nn 2 (by norm_num); dsimp only [CX2]; positivity)
  let C_har : ℝ := 1 / (2 * π) * (15 * C_D * M_tot_w + 4 * κ_min⁻¹ * C_v2) + 1
  refine ⟨c₀, C_har, hc₀_ge_e2, by positivity, ?_⟩
  intro ε c R f hε hc hRlo hRhi hf j hj k hk2 hk_le
  obtain ⟨hcM, hlam_le, hcs_le, hvert, htau_c, hdeg⟩ := hc₀_prop c hc
  have hce2 : Real.exp 2 ≤ c := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hcM))
  have hc_w : c_w ≤ c := (le_max_left _ _).trans hcM
  have hc_x : c_x ≤ c := (le_max_left _ _).trans ((le_max_right _ _).trans hcM)
  have hc_L : cL ≤ c := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hcM))
  have hc1 : 1 < c := lt_of_lt_of_le (by linarith [Real.one_lt_exp_iff.2 (by norm_num : (0 : ℝ) < 2)]) hce2
  have hc0 : 0 < c := by linarith
  have hc32 : 3 / 2 < c := by linarith [Real.one_lt_exp_iff.2 (by norm_num : (0 : ℝ) < 2)]
  have hlog2 : 2 ≤ Real.log c := (Real.le_log_iff_exp_le hc0).2 hce2
  have hM := hankelMass_nonneg hc0 f
  have hc14_nn : 0 ≤ c ^ (-(14 : ℝ)) := Real.rpow_nonneg hc0.le _
  obtain ⟨_, _, _, _, hblock⟩ := hblocks hε hc_w hRlo hRhi
  obtain ⟨hLj_lo, hLj_hi, hℓ0, hℓ_lb, hτ_lb, hτ_pos, hnw_cd, hnw_bd, hnw_supp, hnw_lo, _, hwin, hnw_drv⟩ :=
    hblock j hj
  set Lj := partGrid (ctLv0 c / 4) (j + 1)
  set ℓj := min Lj 1
  set τj := tau0 Lj
  obtain ⟨hL0, _, _, _⟩ := hLv0 c hc_L
  set a₀ : ℝ := max (ctLv0 c / 4) (Lj - ℓj / 100)
  set a' : ℝ := max (ctLv0 c / 3) (Lj - ℓj / 120)
  set b' : ℝ := Lj + ℓj / 120
  set b₀ : ℝ := Lj + ℓj / 100
  by_cases ha'b' : b' < a'
  · have hzero : ∀ L : ℝ, nearWeight ε c R j L = 0 := fun L => by
      by_cases hL1 : L ≤ ctLv0 c / 3
      · exact hnw_lo L hL1
      · by_cases hL2 : L < Lj - ℓj / 120
        · exact hnw_supp L fun h => by linarith only [h.1, hL2]
        · exact hnw_supp L fun h => by
            have : a' ≤ L := max_le (not_le.1 hL1).le (not_lt.1 hL2)
            linarith only [this, ha'b', h.2]
    have hint0 : ∫ L : ℝ, nearWeight ε c R j L * hankelHL c f L * Real.cos ((k : ℝ) * (boasX c ε L + π / 2)) = 0 := by
      simp [hzero]
    rw [hint0, abs_zero]
    positivity
  rw [not_lt] at ha'b'
  have ha₀a' : a₀ < a' := by dsimp only [a₀, a']; exact max_lt_max (by linarith only [hL0]) (by linarith only [hℓ0])
  have hb'b₀ : b' < b₀ := by dsimp only [b', b₀]; linarith only [hℓ0]
  set a : ℝ := (a₀ + a') / 2
  set b : ℝ := (b' + b₀) / 2
  have haa : a₀ < a := by dsimp only [a]; linarith only [ha₀a']
  have haa' : a < a' := by dsimp only [a]; linarith only [ha₀a']
  have hb'b : b' < b := by dsimp only [b]; linarith only [hb'b₀]
  have hbb₀ : b < b₀ := by dsimp only [b]; linarith only [hb'b₀]
  have hba_le1 : b - a ≤ 1 := by
    have hℓ1 : ℓj ≤ 1 := min_le_right _ _
    dsimp only [a, b, a₀, b₀] at *
    linarith only [hbb₀, haa, ha₀a', hb'b₀, hℓ1, le_max_right (ctLv0 c / 4) (Lj - ℓj / 100)]
  set u : ℝ → ℂ := fun L => ((nearWeight ε c R j L : ℝ) : ℂ) * Complex.exp (Complex.I * ((k : ℝ) * boasX c ε L : ℝ))
  have hnw_supp' : ∀ L ∉ Icc a' b', nearWeight ε c R j L = 0 := fun L hL => by
    by_cases h1 : L ≤ ctLv0 c / 3
    · exact hnw_lo L h1
    · rw [not_le] at h1
      exact hnw_supp L fun hc_i => hL ⟨max_le h1.le hc_i.1, hc_i.2⟩
  have hsupp_u : ∀ L ∉ Icc a' b', u L = 0 := fun L hL => by simp [u, hnw_supp' L hL]
  have hcd_u : ContDiff ℝ 2 u := by
    rw [contDiff_iff_contDiffAt]
    intro x
    rcases lt_or_ge x (ctLv0 c / 3) with hlt | hge
    · have hev : u =ᶠ[𝓝 x] fun _ => (0 : ℂ) := by
        filter_upwards [Iio_mem_nhds hlt] with L hL
        simp [u, hnw_lo L (Set.mem_Iio.1 hL).le]
      exact (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq hev
    · have hX_at : ContDiffAt ℝ 2 (boasX c ε) x :=
        (boasX_contDiffOn hε 2).contDiffAt (Ioi_mem_nhds (by linarith only [hL0, hge] : 0 < x))
      have hnw_at : ContDiffAt ℝ 2 (fun L => ((nearWeight ε c R j L : ℝ) : ℂ)) x :=
        (Complex.ofRealCLM.contDiff.comp (hnw_cd 2)).contDiffAt
      have hexp_at : ContDiffAt ℝ 2 (fun L => Complex.exp (Complex.I * ((k : ℝ) * boasX c ε L : ℝ))) x :=
        ((contDiffAt_const (c := Complex.I)).mul
          (Complex.ofRealCLM.contDiff.contDiffAt.comp x ((contDiffAt_const (c := (k : ℝ))).mul hX_at))).cexp
      exact hnw_at.mul hexp_at
  have hh := integrable_hankelHL hc0 hf
  have hcos_le : |∫ L : ℝ, nearWeight ε c R j L * hankelHL c f L * Real.cos ((k : ℝ) * (boasX c ε L + π / 2))| ≤
      ‖∫ L : ℝ, u L * (hankelHL c f L : ℂ)‖ := by
    have hrew : (fun L : ℝ => nearWeight ε c R j L * hankelHL c f L * Real.cos ((k : ℝ) * (boasX c ε L + π / 2))) =
        fun L => (Complex.exp (Complex.I * (((k : ℝ) * (π / 2) : ℝ) : ℂ)) * (u L * (hankelHL c f L : ℂ))).re := by
      ext L
      have hre : (Complex.exp (Complex.I * (((k : ℝ) * (π / 2) : ℝ) : ℂ)) *
          (u L * (hankelHL c f L : ℂ))).re =
          nearWeight ε c R j L * hankelHL c f L *
            (Complex.exp ((((k : ℝ) * (boasX c ε L + π / 2) : ℝ) : ℂ) * Complex.I)).re := by
        simp only [u]
        have hexp : Complex.exp (Complex.I * (((k : ℝ) * (π / 2) : ℝ) : ℂ)) *
            Complex.exp (Complex.I * ((k : ℝ) * boasX c ε L : ℝ)) =
            Complex.exp ((((k : ℝ) * (boasX c ε L + π / 2) : ℝ) : ℂ) * Complex.I) := by
          rw [← Complex.exp_add]; congr 1; push_cast; ring
        rw [show Complex.exp (Complex.I * (((k : ℝ) * (π / 2) : ℝ) : ℂ)) *
              (((nearWeight ε c R j L : ℝ) : ℂ) * Complex.exp (Complex.I * ((k : ℝ) * boasX c ε L : ℝ)) *
                (hankelHL c f L : ℂ)) =
            (((nearWeight ε c R j L * hankelHL c f L : ℝ) : ℂ)) *
              (Complex.exp (Complex.I * (((k : ℝ) * (π / 2) : ℝ) : ℂ)) *
                Complex.exp (Complex.I * ((k : ℝ) * boasX c ε L : ℝ))) by push_cast; ring,
          hexp, Complex.re_ofReal_mul]
      rw [hre, Complex.exp_ofReal_mul_I_re]
    have hu_int_c : Integrable (fun L : ℝ => Complex.exp (Complex.I * (((k : ℝ) * (π / 2) : ℝ) : ℂ)) *
        (u L * (hankelHL c f L : ℂ))) := by
      refine hh.norm.mono'
        ((((continuous_const (y := Complex.exp (Complex.I * (((k : ℝ) * (π / 2) : ℝ) : ℂ)))).mul
            hcd_u.continuous).aestronglyMeasurable).mul
          (Complex.continuous_ofReal.comp_aestronglyMeasurable hh.aestronglyMeasurable) |>.congr
            (ae_of_all _ fun L => by simp only [Pi.mul_apply]; ring))
        (ae_of_all _ fun L => ?_)
      rw [norm_mul, norm_mul,
        show Complex.I * (((k : ℝ) * (π / 2) : ℝ) : ℂ) = (((k : ℝ) * (π / 2) : ℝ) : ℂ) * Complex.I by ring,
        Complex.norm_exp_ofReal_mul_I, one_mul]
      have hnu : ‖u L‖ ≤ 1 := by
        simp only [u, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hnw_bd L).1,
          show Complex.I * ((k : ℝ) * boasX c ε L : ℝ) = (((k : ℝ) * boasX c ε L : ℝ) : ℂ) * Complex.I by push_cast; ring,
          Complex.norm_exp_ofReal_mul_I, mul_one]
        exact (hnw_bd L).2
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (abs_nonneg _) hnu
    have hre_int := integral_re hu_int_c
    simp only [RCLike.re_to_complex] at hre_int
    rw [hrew, hre_int]
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [integral_const_mul, norm_mul,
      show Complex.I * (((k : ℝ) * (π / 2) : ℝ) : ℂ) = (((k : ℝ) * (π / 2) : ℝ) : ℂ) * Complex.I by ring,
      Complex.norm_exp_ofReal_mul_I, one_mul]
  set Tj : ℝ := 3 * τj / 2
  set sj : ℝ := min (τj / 4) (min (1 / 4) (325 * Real.log c / (c * ℓj)))
  have hTj_pos : 0 < Tj := by positivity
  have hsj_pos : 0 < sj := lt_min (by positivity) (lt_min (by norm_num) (by positivity))
  have hsj_τ : sj ≤ τj / 4 := min_le_left _ _
  have hsj_4 : sj ≤ 1 / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hsj_log : sj ≤ 325 * Real.log c / (c * ℓj) := (min_le_right _ _).trans (min_le_right _ _)
  have hfour := hankelHL_compact_fourier hc32 hf haa' ha'b' hb'b hcd_u hsupp_u Lj
  have hshift := hankel_contour_shift_norm_le hc32 hf hε haa' ha'b' hb'b hcd_u hsupp_u hTj_pos hsj_pos hsj_4 Lj
  dsimp only at hshift
  set Φ : ℂ → ℂ := fun ζ =>
    hankelHhat c f ζ * Complex.exp ((c : ℂ) * ζ * (Lj : ℂ)) * boasB0 Lj u c a b ζ
  have hsub_win : ∀ L ∈ Ioo a₀ b₀, ctLv0 c / 4 ≤ L ∧ 0 < L ∧ L ∈ Icc (Lj - ℓj / 100) (Lj + ℓj / 100) := by
    intro L hL
    have hLlv : ctLv0 c / 4 ≤ L := le_trans (le_max_left _ _) hL.1.le
    exact ⟨hLlv, lt_of_lt_of_le (by positivity) hLlv, le_trans (le_max_right _ _) hL.1.le, hL.2.le⟩
  have hk_c2 : (k : ℝ) ≤ c ^ 2 + 1 := by
    have h1 : (k : ℝ) ≤ Nat.ceil (c ^ 2) := by exact_mod_cast hk_le
    have h2 : (Nat.ceil (c ^ 2) : ℝ) < c ^ 2 + 1 := Nat.ceil_lt_add_one (by positivity)
    linarith only [h1, h2]
  have hLj_pos : 0 < Lj := by linarith only [hL0, hLj_lo]
  have hτj_le_c : τj ≤ c := (tau0_le_of_le hLj_pos hLj_hi).trans htau_c
  have hosc_box : ∀ σ ∈ Icc (0 : ℝ) sj, ∀ τ ∈ Icc (-Tj) Tj, (σ = 0 ∨ |τ| = Tj) →
      ‖Φ ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤ 3 * C_D * M_tot_w * hankelMass c f * c ^ (5 - 500 / 21 : ℝ) :=
    fun σ hσ τ hτ hside => central_horiz_osc_bound hCD0 hibp_r hc1 hlog2 hc32 hε hc_x hf hk2
      hκmin_pos hLj_pos hℓ0 hτ_pos rfl hℓ_lb hτ_lb hL0 haa haa' ha'b' hb'b hbb₀ hba_le1
      hsj_pos hsj_τ hsj_4 hsj_log rfl hsub_win (fun L hL => ⟨(hwin L hL).1, (hwin L hL).2.1⟩)
      hnw_cd hnw_supp' hCm0 hnw_drv hMtotw_eq (fun L hL => hx_drv hc_x hε L hL) hCX_nn
      (fun r hr L hL => hx_sym r hr hc_x hε L hL) (fun i => rfl) hlam_le hcs_le hdeg hσ hτ hside
  have htail_bd : ∀ {τ : ℝ}, Tj ≤ |τ| →
      ‖Φ ((sj : ℂ) + (τ : ℂ) * Complex.I)‖ ≤ 3 * hankelMass c f * C_v2 * c ^ (-38 : ℝ) * (τ ^ 2)⁻¹ := by
    intro τ hτ
    have hτne : τ ≠ 0 := fun h => by rw [h, abs_zero] at hτ; linarith only [hτ, hTj_pos]
    have hH_tail : ‖hankelHhat c f ((sj : ℂ) + (τ : ℂ) * Complex.I) *
        Complex.exp ((c : ℂ) * ((sj : ℂ) + (τ : ℂ) * Complex.I) * (Lj : ℂ))‖ ≤
        3 * hankelMass c f * c ^ (-50 : ℝ) := by
      have hS0 := S0_ineq hτ_pos hsj_pos hsj_τ hsj_4 hτ
      have hmL : hankelEdgeM τj = Lj := hankelEdgeM_tau0 hLj_pos
      have hm_mono : hankelEdgeM (3 * τj / 2) ≤ hankelEdgeM |τ| :=
        hankelEdgeM_strictMonoOn.monotoneOn (mem_Ici.2 (by positivity)) (mem_Ici.2 (abs_nonneg _)) hτ
      have hdel := (hankelEdge_delta32_ge_L hτ_pos).2
      rw [hmL] at hS0 hdel
      have hsj_del : c * (stripS0Tilde ((sj : ℂ) + (τ : ℂ) * Complex.I)).re + c * sj * Lj ≤ -50 * Real.log c := by
        have hstep1 : (stripS0Tilde ((sj : ℂ) + (τ : ℂ) * Complex.I)).re + sj * Lj ≤ -(2 / 13) * sj * ℓj := by
          have h1 : 5 / 26 * ℓj ≤ hankelEdgeM |τ| - Lj := le_trans hdel (by linarith only [hm_mono])
          nlinarith only [hS0, hsj_pos, h1]
        have h50 : 50 * Real.log c ≤ 2 / 13 * c * sj * ℓj := by
          rcases le_total (τj / 4) (min (1 / 4) (325 * Real.log c / (c * ℓj))) with hs1 | hs23
          · have hs_eq : sj = τj / 4 := min_eq_left hs1
            have h1 : 50 * Real.log c ≤ 1 / 26 * κ_min ^ 2 * c ^ (6 / 7 : ℝ) := hvert.1
            have hpow : c * c ^ (-(1 / 21 : ℝ)) * c ^ (-(2 / 21 : ℝ)) = c ^ (6 / 7 : ℝ) := by
              nth_rw 1 [← Real.rpow_one c]; rw [← Real.rpow_add hc0, ← Real.rpow_add hc0]; norm_num
            have h2 : 1 / 26 * κ_min ^ 2 * c ^ (6 / 7 : ℝ) ≤ 2 / 13 * c * sj * ℓj := by
              rw [hs_eq]
              calc 1 / 26 * κ_min ^ 2 * c ^ (6 / 7 : ℝ)
                  = 2 / 13 * c * (κ_min * c ^ (-(1 / 21 : ℝ)) / 4) * (κ_min * c ^ (-(2 / 21 : ℝ))) := by
                    rw [← hpow]; ring
                _ ≤ 2 / 13 * c * (τj / 4) * ℓj := by gcongr
            linarith only [h1, h2]
          · have hs_eq : sj = min (1 / 4) (325 * Real.log c / (c * ℓj)) := min_eq_right hs23
            rw [hs_eq]
            rcases le_total (1 / 4) (325 * Real.log c / (c * ℓj)) with h14 | hlog_min
            · rw [min_eq_left h14]
              have h1 : 50 * Real.log c ≤ 1 / 26 * κ_min * c ^ (19 / 21 : ℝ) := hvert.2
              have hpow : c * c ^ (-(2 / 21 : ℝ)) = c ^ (19 / 21 : ℝ) := by
                nth_rw 1 [← Real.rpow_one c]; rw [← Real.rpow_add hc0]; norm_num
              have h2 : 1 / 26 * κ_min * c ^ (19 / 21 : ℝ) ≤ 2 / 13 * c * (1 / 4) * ℓj := by
                calc 1 / 26 * κ_min * c ^ (19 / 21 : ℝ) = 2 / 13 * c * (1 / 4) * (κ_min * c ^ (-(2 / 21 : ℝ))) := by
                      rw [← hpow]; ring
                  _ ≤ 2 / 13 * c * (1 / 4) * ℓj := by gcongr
              linarith only [h1, h2]
            · rw [min_eq_right hlog_min]
              field_simp [hc0.ne', hℓ0.ne']; norm_num
        nlinarith only [hstep1, h50, hc0]
      have hexp_50 : Real.exp (c * (stripS0Tilde ((sj : ℂ) + (τ : ℂ) * Complex.I)).re + c * sj * Lj) ≤
          c ^ (-50 : ℝ) := by
        calc Real.exp (c * (stripS0Tilde ((sj : ℂ) + (τ : ℂ) * Complex.I)).re + c * sj * Lj)
            ≤ Real.exp (-50 * Real.log c) := Real.exp_le_exp.2 hsj_del
          _ = c ^ (-50 : ℝ) := by rw [show -50 * Real.log c = Real.log c * (-50) by ring, ← Real.rpow_def_of_pos hc0]
      rw [norm_mul, Complex.norm_exp,
        show ((c : ℂ) * ((sj : ℂ) + (τ : ℂ) * Complex.I) * (Lj : ℂ)).re = c * sj * Lj by
          simp [Complex.mul_re, Complex.mul_im] ]
      have hbnd := hankelHhat_bound hc32 hf hε hsj_pos.le hsj_4 τ
      calc ‖hankelHhat c f ((sj : ℂ) + (τ : ℂ) * Complex.I)‖ * Real.exp (c * sj * Lj)
          ≤ 3 * hankelMass c f * Real.exp (c * (stripS0Tilde ((sj : ℂ) + (τ : ℂ) * Complex.I)).re + c * sj * Lj) :=
            (mul_le_mul_of_nonneg_right hbnd (Real.exp_pos (c * sj * Lj)).le).trans_eq
              (by rw [mul_assoc (3 * hankelMass c f), ← Real.exp_add])
        _ ≤ 3 * hankelMass c f * c ^ (-50 : ℝ) := by gcongr
    have hB_tail := vertical_tail_ibp_bound hc1 hlog2 hε hc_x hk_c2 hκmin_pos hℓ0 hℓ_lb hτj_le_c hL0
      haa haa' ha'b' hb'b hbb₀ hba_le1 hsj_pos hsj_log hτne hsub_win (fun L hL => (hwin L hL).2.1)
      hnw_cd hnw_supp' hCm0 hnw_drv hMtot2_eq (hCX_nn 2 (by norm_num)) rfl
      (fun L hL => hx_drv hc_x hε L hL) (fun L hL => hx_sym 2 (by norm_num) hc_x hε L hL)
      hlam_le hcs_le hcd_u
    rw [norm_mul]
    calc ‖hankelHhat c f ((sj : ℂ) + (τ : ℂ) * Complex.I) *
            Complex.exp ((c : ℂ) * ((sj : ℂ) + (τ : ℂ) * Complex.I) * (Lj : ℂ))‖ *
          ‖boasB0 Lj u c a b ((sj : ℂ) + (τ : ℂ) * Complex.I)‖
        ≤ (3 * hankelMass c f * c ^ (-50 : ℝ)) * (C_v2 * c ^ (12 : ℝ) * (τ ^ 2)⁻¹) := by gcongr
      _ = 3 * hankelMass c f * C_v2 * c ^ (-38 : ℝ) * (τ ^ 2)⁻¹ := by
          have hc5012 : c ^ (-50 : ℝ) * c ^ (12 : ℝ) = c ^ (-38 : ℝ) := by rw [← Real.rpow_add hc0]; norm_num
          calc _ = 3 * hankelMass c f * C_v2 * (c ^ (-50 : ℝ) * c ^ (12 : ℝ)) * (τ ^ 2)⁻¹ := by ring
            _ = _ := by rw [hc5012]
  have hpiece_mid : ∫ τ in Icc (-Tj) Tj, ‖Φ ((τ : ℂ) * Complex.I)‖ ≤
      9 * C_D * M_tot_w * hankelMass c f * c ^ (6 - 500 / 21 : ℝ) := by
    have hconst := setIntegral_mono_on hshift.1
      (continuousOn_const (c := 3 * C_D * M_tot_w * hankelMass c f * c ^ (5 - 500 / 21 : ℝ))).integrableOn_Icc
      measurableSet_Icc fun τ hτ => by
        have h0 := hosc_box 0 ⟨le_rfl, hsj_pos.le⟩ τ hτ (Or.inl rfl)
        simp only [Complex.ofReal_zero, zero_add] at h0
        exact h0
    refine hconst.trans ?_
    rw [setIntegral_const, smul_eq_mul, Real.volume_real_Icc_of_le (by linarith only [hTj_pos]),
      show Tj - -Tj = 3 * τj by simp only [Tj]; ring]
    have h6 : c * c ^ (5 - 500 / 21 : ℝ) = c ^ (6 - 500 / 21 : ℝ) := by
      nth_rw 1 [← Real.rpow_one c]; rw [← Real.rpow_add hc0]; ring_nf
    calc (3 * τj) * (3 * C_D * M_tot_w * hankelMass c f * c ^ (5 - 500 / 21 : ℝ))
        ≤ (3 * c) * (3 * C_D * M_tot_w * hankelMass c f * c ^ (5 - 500 / 21 : ℝ)) := by gcongr
      _ = 9 * C_D * M_tot_w * hankelMass c f * (c * c ^ (5 - 500 / 21 : ℝ)) := by ring
      _ = _ := by rw [h6]
  have hpiece_topH : ∫ σ in (0 : ℝ)..sj, ‖Φ ((σ : ℂ) + (Tj : ℂ) * Complex.I)‖ ≤
      3 * C_D * M_tot_w * hankelMass c f * c ^ (6 - 500 / 21 : ℝ) := by
    rw [intervalIntegral.integral_of_le hsj_pos.le]
    have hmono : IntegrableOn (fun σ : ℝ => ‖Φ ((σ : ℂ) + (Tj : ℂ) * Complex.I)‖) (Ioc 0 sj) :=
      hshift.2.1.1
    have hconst_int : IntegrableOn
        (fun _ : ℝ => 3 * C_D * M_tot_w * hankelMass c f * c ^ (5 - 500 / 21 : ℝ)) (Ioc 0 sj) :=
      (continuousOn_const : ContinuousOn
        (fun _ : ℝ => 3 * C_D * M_tot_w * hankelMass c f * c ^ (5 - 500 / 21 : ℝ)) (Icc 0 sj)).integrableOn_Icc.mono_set
        Ioc_subset_Icc_self
    have hconst := setIntegral_mono_on hmono hconst_int
      measurableSet_Ioc fun σ hσ =>
        hosc_box σ ⟨hσ.1.le, hσ.2⟩ Tj ⟨by linarith only [hTj_pos], le_rfl⟩ (Or.inr (abs_of_pos hTj_pos))
    refine hconst.trans ?_
    rw [setIntegral_const, smul_eq_mul, Real.volume_real_Ioc_of_le hsj_pos.le, sub_zero]
    have h1 : sj ≤ c := by linarith only [hsj_4, hc1]
    have h6 : c * c ^ (5 - 500 / 21 : ℝ) = c ^ (6 - 500 / 21 : ℝ) := by
      nth_rw 1 [← Real.rpow_one c]; rw [← Real.rpow_add hc0]; ring_nf
    calc sj * (3 * C_D * M_tot_w * hankelMass c f * c ^ (5 - 500 / 21 : ℝ))
        ≤ c * (3 * C_D * M_tot_w * hankelMass c f * c ^ (5 - 500 / 21 : ℝ)) := by gcongr
      _ = 3 * C_D * M_tot_w * hankelMass c f * (c * c ^ (5 - 500 / 21 : ℝ)) := by ring
      _ = _ := by rw [h6]
  have hpiece_botH : ∫ σ in (0 : ℝ)..sj, ‖Φ ((σ : ℂ) + (-Tj : ℝ) * Complex.I)‖ ≤
      3 * C_D * M_tot_w * hankelMass c f * c ^ (6 - 500 / 21 : ℝ) := by
    rw [intervalIntegral.integral_of_le hsj_pos.le]
    have hmono : IntegrableOn (fun σ : ℝ => ‖Φ ((σ : ℂ) + (-Tj : ℝ) * Complex.I)‖) (Ioc 0 sj) :=
      hshift.2.2.1.1
    have hconst_int : IntegrableOn
        (fun _ : ℝ => 3 * C_D * M_tot_w * hankelMass c f * c ^ (5 - 500 / 21 : ℝ)) (Ioc 0 sj) :=
      (continuousOn_const : ContinuousOn
        (fun _ : ℝ => 3 * C_D * M_tot_w * hankelMass c f * c ^ (5 - 500 / 21 : ℝ)) (Icc 0 sj)).integrableOn_Icc.mono_set
        Ioc_subset_Icc_self
    have hconst := setIntegral_mono_on hmono hconst_int
      measurableSet_Ioc fun σ hσ =>
        hosc_box σ ⟨hσ.1.le, hσ.2⟩ (-Tj) ⟨le_rfl, by linarith only [hTj_pos]⟩
          (Or.inr (by rw [abs_neg, abs_of_pos hTj_pos]))
    refine hconst.trans ?_
    rw [setIntegral_const, smul_eq_mul, Real.volume_real_Ioc_of_le hsj_pos.le, sub_zero]
    have h1 : sj ≤ c := by linarith only [hsj_4, hc1]
    have h6 : c * c ^ (5 - 500 / 21 : ℝ) = c ^ (6 - 500 / 21 : ℝ) := by
      nth_rw 1 [← Real.rpow_one c]; rw [← Real.rpow_add hc0]; ring_nf
    calc sj * (3 * C_D * M_tot_w * hankelMass c f * c ^ (5 - 500 / 21 : ℝ))
        ≤ c * (3 * C_D * M_tot_w * hankelMass c f * c ^ (5 - 500 / 21 : ℝ)) := by gcongr
      _ = 3 * C_D * M_tot_w * hankelMass c f * (c * c ^ (5 - 500 / 21 : ℝ)) := by ring
      _ = _ := by rw [h6]
  have hinvsq_Ioi : IntegrableOn (fun τ : ℝ => (τ ^ 2)⁻¹) (Ioi Tj) := by
    refine (integrable_inv_one_add_sq.const_mul (1 + Tj⁻¹ ^ 2)).integrableOn.mono'
      ((measurable_id.pow_const 2).inv.aestronglyMeasurable) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun τ (hτ : Tj < τ) => ?_)
    have hτ2 : Tj ^ 2 ≤ τ ^ 2 := by nlinarith only [hTj_pos, hτ]
    have h1 : 1 ≤ Tj⁻¹ ^ 2 * τ ^ 2 := by rw [inv_pow, inv_mul_eq_div, one_le_div (by positivity)]; exact hτ2
    rw [Real.norm_of_nonneg (by positivity), ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    calc (τ ^ 2)⁻¹ * (1 + τ ^ 2) ≤ (τ ^ 2)⁻¹ * ((1 + Tj⁻¹ ^ 2) * τ ^ 2) := by gcongr; linarith
      _ = 1 + Tj⁻¹ ^ 2 := by
        field_simp [pow_ne_zero 2 (lt_trans hTj_pos hτ).ne']
        rw [div_self (lt_trans hTj_pos hτ).ne']
  have hinvsq_Iio : IntegrableOn (fun τ : ℝ => (τ ^ 2)⁻¹) (Iio (-Tj)) := by
    refine (integrable_inv_one_add_sq.const_mul (1 + Tj⁻¹ ^ 2)).integrableOn.mono'
      ((measurable_id.pow_const 2).inv.aestronglyMeasurable) ?_
    refine (ae_restrict_iff' measurableSet_Iio).2 (ae_of_all _ fun τ (hτ : τ < -Tj) => ?_)
    have hτ2 : Tj ^ 2 ≤ τ ^ 2 := by nlinarith only [hTj_pos, hτ]
    have h1 : 1 ≤ Tj⁻¹ ^ 2 * τ ^ 2 := by rw [inv_pow, inv_mul_eq_div, one_le_div (by positivity)]; exact hτ2
    rw [Real.norm_of_nonneg (by positivity), ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    calc (τ ^ 2)⁻¹ * (1 + τ ^ 2) ≤ (τ ^ 2)⁻¹ * ((1 + Tj⁻¹ ^ 2) * τ ^ 2) := by gcongr; linarith
      _ = 1 + Tj⁻¹ ^ 2 := by
        have hτn : τ ≠ 0 := by linarith only [hτ, hTj_pos]
        field_simp [pow_ne_zero 2 hτn]
  have hTj_inv : Tj⁻¹ ≤ (2 / 3) * κ_min⁻¹ * c ^ (1 / 21 : ℝ) := by
    have hc121 : c ^ (-(1 / 21 : ℝ)) * c ^ (1 / 21 : ℝ) = 1 := by rw [← Real.rpow_add hc0]; norm_num
    rw [show Tj = 3 / 2 * τj by simp only [Tj]; ring, inv_eq_one_div, div_le_iff₀' (by positivity)]
    calc 1 = (3 / 2 * (κ_min * c ^ (-(1 / 21 : ℝ)))) * ((2 / 3 : ℝ) * κ_min⁻¹ * c ^ (1 / 21 : ℝ)) := by
          rw [show (3 / 2 * (κ_min * c ^ (-(1 / 21 : ℝ)))) * ((2 / 3 : ℝ) * κ_min⁻¹ * c ^ (1 / 21 : ℝ)) =
              (3 / 2 * (2 / 3)) * (κ_min * κ_min⁻¹) * (c ^ (-(1 / 21 : ℝ)) * c ^ (1 / 21 : ℝ)) by ring,
            mul_inv_cancel₀ hκmin_pos.ne', hc121]; norm_num
      _ ≤ (3 / 2 * τj) * ((2 / 3 : ℝ) * κ_min⁻¹ * c ^ (1 / 21 : ℝ)) := by gcongr
  have hpiece_topV : ∫ τ in Ioi Tj, ‖Φ ((sj : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
      2 * κ_min⁻¹ * C_v2 * hankelMass c f * c ^ (-37 : ℝ) := by
    have hm := setIntegral_mono_on hshift.2.2.2.1 (hinvsq_Ioi.const_mul _) measurableSet_Ioi fun τ (hτ : Tj < τ) =>
      htail_bd (le_trans hτ.le (le_abs_self τ))
    refine hm.trans ?_
    rw [integral_const_mul, integral_Ioi_inv_sq hTj_pos]
    have hc38 : c ^ (-38 : ℝ) * c ^ (1 / 21 : ℝ) ≤ c ^ (-37 : ℝ) := by
      rw [← Real.rpow_add hc0]; exact Real.rpow_le_rpow_of_exponent_le hc1.le (by norm_num)
    calc 3 * hankelMass c f * C_v2 * c ^ (-38 : ℝ) * Tj⁻¹
        ≤ 3 * hankelMass c f * C_v2 * c ^ (-38 : ℝ) * ((2 / 3) * κ_min⁻¹ * c ^ (1 / 21 : ℝ)) := by gcongr
      _ = 2 * κ_min⁻¹ * C_v2 * hankelMass c f * (c ^ (-38 : ℝ) * c ^ (1 / 21 : ℝ)) := by ring
      _ ≤ _ := by gcongr
  have hpiece_botV : ∫ τ in Iio (-Tj), ‖Φ ((sj : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
      2 * κ_min⁻¹ * C_v2 * hankelMass c f * c ^ (-37 : ℝ) := by
    have hm := setIntegral_mono_on hshift.2.2.2.2.1 (hinvsq_Iio.const_mul _) measurableSet_Iio fun τ (hτ : τ < -Tj) =>
      htail_bd (by rw [abs_of_neg (by linarith only [hτ, hTj_pos])]; linarith only [hτ])
    refine hm.trans ?_
    rw [integral_const_mul, integral_Iio_inv_sq hTj_pos]
    have hc38 : c ^ (-38 : ℝ) * c ^ (1 / 21 : ℝ) ≤ c ^ (-37 : ℝ) := by
      rw [← Real.rpow_add hc0]; exact Real.rpow_le_rpow_of_exponent_le hc1.le (by norm_num)
    calc 3 * hankelMass c f * C_v2 * c ^ (-38 : ℝ) * Tj⁻¹
        ≤ 3 * hankelMass c f * C_v2 * c ^ (-38 : ℝ) * ((2 / 3) * κ_min⁻¹ * c ^ (1 / 21 : ℝ)) := by gcongr
      _ = 2 * κ_min⁻¹ * C_v2 * hankelMass c f * (c ^ (-38 : ℝ) * c ^ (1 / 21 : ℝ)) := by ring
      _ ≤ _ := by gcongr
  refine hcos_le.trans ?_
  rw [hfour.2, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity : 0 ≤ c / (2 * π))]
  have hc17 : c ^ (6 - 500 / 21 : ℝ) ≤ c ^ (-15 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hc1.le (by norm_num)
  have hc37 : c ^ (-37 : ℝ) ≤ c ^ (-15 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hc1.le (by norm_num)
  have hsum_phi : ‖∫ τ : ℝ, Φ ((τ : ℂ) * Complex.I)‖ ≤
      (15 * C_D * M_tot_w + 4 * κ_min⁻¹ * C_v2) * hankelMass c f * c ^ (-15 : ℝ) := by
    refine hshift.2.2.2.2.2.trans ?_
    calc (∫ τ in Icc (-Tj) Tj, ‖Φ ((τ : ℂ) * Complex.I)‖) +
          (∫ σ in (0 : ℝ)..sj, ‖Φ ((σ : ℂ) + (Tj : ℂ) * Complex.I)‖) +
          (∫ σ in (0 : ℝ)..sj, ‖Φ ((σ : ℂ) + (-Tj : ℝ) * Complex.I)‖) +
          (∫ τ in Ioi Tj, ‖Φ ((sj : ℂ) + (τ : ℂ) * Complex.I)‖) +
          (∫ τ in Iio (-Tj), ‖Φ ((sj : ℂ) + (τ : ℂ) * Complex.I)‖)
        ≤ 9 * C_D * M_tot_w * hankelMass c f * c ^ (6 - 500 / 21 : ℝ) +
          3 * C_D * M_tot_w * hankelMass c f * c ^ (6 - 500 / 21 : ℝ) +
          3 * C_D * M_tot_w * hankelMass c f * c ^ (6 - 500 / 21 : ℝ) +
          2 * κ_min⁻¹ * C_v2 * hankelMass c f * c ^ (-37 : ℝ) +
          2 * κ_min⁻¹ * C_v2 * hankelMass c f * c ^ (-37 : ℝ) := by
            linarith only [hpiece_mid, hpiece_topH, hpiece_botH, hpiece_topV, hpiece_botV]
      _ ≤ 15 * C_D * M_tot_w * hankelMass c f * c ^ (-15 : ℝ) +
          4 * κ_min⁻¹ * C_v2 * hankelMass c f * c ^ (-15 : ℝ) := by
            have h1 : 15 * C_D * M_tot_w * hankelMass c f * c ^ (6 - 500 / 21 : ℝ) ≤
                15 * C_D * M_tot_w * hankelMass c f * c ^ (-15 : ℝ) := by gcongr
            have h2 : 4 * κ_min⁻¹ * C_v2 * hankelMass c f * c ^ (-37 : ℝ) ≤
                4 * κ_min⁻¹ * C_v2 * hankelMass c f * c ^ (-15 : ℝ) := by gcongr
            linarith only [h1, h2]
      _ = _ := by ring
  have hc14 : c * c ^ (-15 : ℝ) = c ^ (-(14 : ℝ)) := by
    nth_rw 1 [← Real.rpow_one c]; rw [← Real.rpow_add hc0]; norm_num
  calc c / (2 * π) * ‖∫ τ : ℝ, Φ ((τ : ℂ) * Complex.I)‖
      ≤ c / (2 * π) * ((15 * C_D * M_tot_w + 4 * κ_min⁻¹ * C_v2) * hankelMass c f * c ^ (-15 : ℝ)) :=
        mul_le_mul_of_nonneg_left hsum_phi (by positivity)
    _ = 1 / (2 * π) * (15 * C_D * M_tot_w + 4 * κ_min⁻¹ * C_v2) * hankelMass c f * (c * c ^ (-15 : ℝ)) := by ring
    _ ≤ C_har * hankelMass c f * c ^ (-(14 : ℝ)) := by
        rw [hc14]; dsimp only [C_har]; gcongr; linarith

/-- info: 'FormalResearch.SignUncertainty.boas_harmonic_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms boas_harmonic_bound

end FormalResearch.SignUncertainty
