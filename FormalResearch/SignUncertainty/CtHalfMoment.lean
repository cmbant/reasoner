module

public import FormalResearch.SignUncertainty.CtScaleBoot
public import FormalResearch.SignUncertainty.HankelBootData
public import FormalResearch.SignUncertainty.HankelQuantC1Feasible
public import FormalResearch.SignUncertainty.HankelBootCircle
public import FormalResearch.SignUncertainty.CtBoasMoments
public import FormalResearch.SignUncertainty.CtBandTop
public import FormalResearch.Asymptotics.DyadicAbsorption

/-!
# Scale-`r` Dyadic Absorption and Negative Half-Moment (`ct:dyadic` Step 1c & `ct:half` (1))

Combines `CtScaleBoot.hankel_scale_mass_step` with `Asymptotics.absorb_dyadic` to prove:
1. `hankel_scale_dyadic_bound`: `B₁(s; f, u_T) ≤ C_dyad * s^{-1/2}` at every scale
   `s ∈ [r_min_base (log c)², R_J]` (and `B₁(r) + B₂(r) ≤ C_dyad * r^{-1/2}` at every good
   circle `r` in that range).
2. `hankel_neg_half_moment_le`: for `0 ≤ R' ≤ 10⁻⁴ c^{2/3}`,
   `∫ v in Set.Ioo 0 R', (1 + v)^{1/2} |Re Ψ̃(-v)| dv ≤ C_half * log c`
   (splitting at `r_min` via `hankel_psi_abs_mass` and summing `O(log c)` dyadic blocks
   `[2^j r_min, min (2^{j+1} r_min) R_J]` via `hankelBoot_R_mul_B1` and `hankelPsiR_sub_Q_le`).
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped Real Interval

namespace FormalResearch.SignUncertainty

open FormalResearch.Special
open FormalResearch.Asymptotics

private lemma halfMoment_log_ge_32 {c : ℝ} (hc : 1e14 ≤ c) : 32 ≤ Real.log c := by
  have hc0 : 0 < c := by linarith
  have hexp1 : Real.exp 1 ≤ 2.72 := by linarith [Real.exp_one_lt_d9]
  have hexp32 : Real.exp 32 ≤ c := by
    have h3 : Real.exp (32 : ℝ) = (Real.exp 1) ^ (32 : ℕ) := by
      rw [← Real.exp_nat_mul]; norm_num
    have h4 : (2.72 : ℝ) ^ (32 : ℕ) ≤ 1e14 := by norm_num
    calc Real.exp 32 = (Real.exp 1) ^ (32 : ℕ) := h3
      _ ≤ (2.72 : ℝ) ^ (32 : ℕ) := pow_le_pow_left₀ (Real.exp_pos 1).le hexp1 32
      _ ≤ 1e14 := h4
      _ ≤ c := hc
  exact (Real.le_log_iff_exp_le hc0).2 hexp32

private lemma hankelBoot_psiLead_nonneg {c ε T u_T x : ℝ} {f : ℝ → ℝ}
    (hc0 : 0 < c) (hf : IsHankelFeasible c ε T f)
    (hT : c * hankelXi c u_T = T) (huA : |u_T| ≤ langerRadius c)
    (hxA : |x| ≤ langerRadius c) (hx : x ≤ u_T) :
    0 ≤ hankelPsiLead c f x := by
  have hxi_d : hankelXiD c x < 0 := hankelXiD_neg hc0 hxA
  have hxi_pos : 0 < hankelXi c x := hankelXi_pos hc0 hxA
  have hcxi_ge : T ≤ c * hankelXi c x := by
    rw [← hT]
    exact hankel_phi_anti hc0 hxA huA hx
  have htail : 0 ≤ f (c * hankelXi c x) := hf.tail_nonneg _ hcxi_ge
  have hrho : 0 ≤ hankelRho0 c (c * hankelXi c x) :=
    hankelRho0_nonneg hc0 (mul_pos hc0 hxi_pos).le
  unfold hankelPsiLead
  have hcxd : 0 ≤ -(c * hankelXiD c x) := by nlinarith [hc0, hxi_d]
  exact mul_nonneg hcxd (mul_nonneg hrho htail)

private lemma hankelBoot_r_mul_B1_mono {c ε T u_T r₁ r₂ : ℝ} {f : ℝ → ℝ}
    (hc0 : 0 < c) (hf : IsHankelFeasible c ε T f)
    (hT : c * hankelXi c u_T = T) (huA : |u_T| ≤ langerRadius c)
    (hr₁ : 0 < r₁) (hrr : r₁ ≤ r₂) (hr₂A : r₂ ≤ langerRadius c) (hru : -r₁ ≤ u_T) :
    r₁ * hankelBootB1 c f r₁ u_T ≤ r₂ * hankelBootB1 c f r₂ u_T := by
  have hfe := hf.toIsHankelEigenfn
  have hr₂ : 0 < r₂ := lt_of_lt_of_le hr₁ hrr
  have hr₁A : r₁ ≤ langerRadius c := hrr.trans hr₂A
  have hr₂u : -r₂ ≤ u_T := by linarith
  rw [hankelBoot_R_mul_B1 hc0 hf hT huA hr₁A hr₁ hru,
    hankelBoot_R_mul_B1 hc0 hf hT huA hr₂A hr₂ hr₂u]
  have hQcont : ContinuousOn (fun x : ℝ => (-x) * hankelPsiLead c f x)
      (Icc (-langerRadius c) (langerRadius c)) :=
    (continuousOn_id.neg).mul (continuousOn_hankelQ hc0 hfe)
  have i1 : IntervalIntegrable (fun x : ℝ => (-x) * hankelPsiLead c f x) volume (-r₂) (-r₁) :=
    (hQcont.mono (Icc_subset_Icc (by linarith) (by linarith))).intervalIntegrable_of_Icc
      (μ := volume) (by linarith)
  have i2 : IntervalIntegrable (fun x : ℝ => (-x) * hankelPsiLead c f x) volume (-r₁) u_T :=
    (hQcont.mono (Icc_subset_Icc (by linarith) (abs_le.1 huA).2)).intervalIntegrable_of_Icc
      (μ := volume) hru
  rw [← intervalIntegral.integral_add_adjacent_intervals i1 i2]
  have hnn : 0 ≤ ∫ x in (-r₂)..(-r₁), (-x) * hankelPsiLead c f x := by
    refine intervalIntegral.integral_nonneg (by linarith) fun x hx => ?_
    have hxA : |x| ≤ langerRadius c := by rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
    exact mul_nonneg (by linarith [hx.2])
      (hankelBoot_psiLead_nonneg hc0 hf hT huA hxA (hx.2.trans hru))
  linarith only [hnn]

private lemma hankelScale_snap_B1 {c ε T u_T s r' C : ℝ} {f : ℝ → ℝ}
    (hc3 : 3e6 ≤ c) (hf : IsHankelFeasible c ε T f) (hε : ε = 1 ∨ ε = -1)
    (hmass : hankelMass c f = 1) (hT : c * hankelXi c u_T = T)
    (hu0 : u_T ≤ 0) (hu3 : -3 ≤ u_T) (huA : |u_T| ≤ langerRadius c)
    (hs10 : 10 ≤ s) (hsr' : s ≤ r') (hr's : r' ≤ s + 1) (hr'A : r' ≤ langerRadius c)
    (hC_nn : 0 ≤ C)
    (hC_pair : r' ^ (1 / 2 : ℝ) * (hankelBootB1 c f r' u_T + hankelBootB2 c f r') ≤ C) :
    s ^ (1 / 2 : ℝ) * hankelBootB1 c f s u_T ≤ 2 * C ∧
      hankelBootB1 c f s u_T ≤ 2 * C * s ^ (-(1 / 2 : ℝ)) := by
  have hc0 : 0 < c := by linarith
  have hs0 : 0 < s := by linarith
  have hr'0 : 0 < r' := by linarith
  have hsu : -s ≤ u_T := by linarith
  have hr'u : -r' ≤ u_T := by linarith
  have hB1_nn : 0 ≤ hankelBootB1 c f r' u_T :=
    hankelBootB1_nonneg hc3 hf hε hmass hT hu0 hu3 hr'0 hr'u hr'A
  have hB2_nn : 0 ≤ hankelBootB2 c f r' := hankelBootB2_nonneg c f r'
  have hC_B1 : r' ^ (1 / 2 : ℝ) * hankelBootB1 c f r' u_T ≤ C :=
    (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hB2_nn) (Real.rpow_nonneg hr'0.le _)).trans
      hC_pair
  have hpos12 : 0 < r' ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hr'0 _
  have hC : hankelBootB1 c f r' u_T ≤ C * r' ^ (-(1 / 2 : ℝ)) := by
    rw [Real.rpow_neg hr'0.le]
    calc hankelBootB1 c f r' u_T
        = (r' ^ (1 / 2 : ℝ))⁻¹ * (r' ^ (1 / 2 : ℝ) * hankelBootB1 c f r' u_T) := by
          rw [← mul_assoc, inv_mul_cancel₀ hpos12.ne', one_mul]
      _ ≤ (r' ^ (1 / 2 : ℝ))⁻¹ * C := mul_le_mul_of_nonneg_left hC_B1 (by positivity)
      _ = C * (r' ^ (1 / 2 : ℝ))⁻¹ := by ring
  have hmono : s * hankelBootB1 c f s u_T ≤ r' * hankelBootB1 c f r' u_T :=
    hankelBoot_r_mul_B1_mono hc0 hf hT huA hs0 hsr' hr'A hsu
  have h_B1_div : hankelBootB1 c f s u_T ≤ (r' / s) * hankelBootB1 c f r' u_T := by
    calc hankelBootB1 c f s u_T = s⁻¹ * (s * hankelBootB1 c f s u_T) := by
          rw [← mul_assoc, inv_mul_cancel₀ hs0.ne', one_mul]
      _ ≤ s⁻¹ * (r' * hankelBootB1 c f r' u_T) := mul_le_mul_of_nonneg_left hmono (by positivity)
      _ = (r' / s) * hankelBootB1 c f r' u_T := by ring
  have hr's2 : r' / s ≤ 2 := by rw [div_le_iff₀ hs0]; linarith
  have h_r12_mono : r' ^ (-(1 / 2 : ℝ)) ≤ s ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hs0 hsr' (by norm_num)
  have hB1_s : hankelBootB1 c f s u_T ≤ 2 * C * s ^ (-(1 / 2 : ℝ)) := by
    calc hankelBootB1 c f s u_T ≤ (r' / s) * hankelBootB1 c f r' u_T := h_B1_div
      _ ≤ 2 * (C * r' ^ (-(1 / 2 : ℝ))) := mul_le_mul hr's2 hC hB1_nn (by norm_num)
      _ ≤ 2 * (C * s ^ (-(1 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h_r12_mono hC_nn) (by norm_num)
      _ = 2 * C * s ^ (-(1 / 2 : ℝ)) := by ring
  refine ⟨?_, hB1_s⟩
  have hs12_mul : s ^ (1 / 2 : ℝ) * s ^ (-(1 / 2 : ℝ)) = 1 := by
    rw [← Real.rpow_add hs0]; norm_num
  calc s ^ (1 / 2 : ℝ) * hankelBootB1 c f s u_T
      ≤ s ^ (1 / 2 : ℝ) * (2 * C * s ^ (-(1 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left hB1_s (Real.rpow_nonneg hs0.le _)
    _ = 2 * C * (s ^ (1 / 2 : ℝ) * s ^ (-(1 / 2 : ℝ))) := by ring
    _ = 2 * C := by rw [hs12_mul, mul_one]

/-- **Scale-`r` dyadic mass bound (`constant_terms_lower.tex`, `ct:dyadic` Part (1), Step 1c)**:
there exist constants `C_dyad > 0`, `r_min_base ≥ 256`, and `c₀ ≥ 1e14` such that for every
`c ≥ c₀`, every feasible normalized Hankel eigenfunction `(f, T)` with `T < cξ(a₁)`,
`u_T` given by `hankel_quantC1_of_feasible`, every `R_J ∈ [10⁻⁴ c^{2/3}, 10⁻⁴ c^{2/3} + 1]`
with `ctGoodRadius R_J`, and every scale `s ∈ [r_min_base (log c)², R_J]`,
`B₁(s; f, u_T) ≤ C_dyad * s^{-1/2}` (and at good circles `r`, `B₁(r) + B₂(r) ≤ C_dyad * r^{-1/2}`). -/
theorem hankel_scale_dyadic_bound :
    ∃ C_dyad r_min_base c₀ : ℝ, 0 < C_dyad ∧ 256 ≤ r_min_base ∧ 1e14 ≤ c₀ ∧
      ∀ (c ε T R_J : ℝ) (f : ℝ → ℝ), c₀ ≤ c →
        IsHankelFeasible c ε T f → (ε = 1 ∨ ε = -1) → hankelMass c f = 1 →
        T < c * hankelXi c (airyZero 1) →
        (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) ≤ R_J →
        R_J ≤ (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) + 1 →
        ctGoodRadius R_J →
        ∃ u_T : ℝ, airyZero 1 < u_T ∧ u_T ≤ langerRadius c ∧ c * hankelXi c u_T = T ∧
          u_T ≤ 0 ∧ -3 ≤ u_T ∧ r_min_base * (Real.log c) ^ 2 ≤ R_J ∧
          (∀ r : ℝ, r_min_base * (Real.log c) ^ 2 ≤ r → r ≤ R_J → ctGoodRadius r →
            hankelBootB1 c f r u_T + hankelBootB2 c f r ≤ C_dyad * r ^ (-(1 / 2 : ℝ))) ∧
          (∀ s : ℝ, r_min_base * (Real.log c) ^ 2 ≤ s → s ≤ R_J →
            hankelBootB1 c f s u_T ≤ C_dyad * s ^ (-(1 / 2 : ℝ))) := by
  obtain ⟨C_step, r_min_base, hC_step_pos, hr_min_base, hstep⟩ := hankel_scale_mass_step
  have hexp_lim : Tendsto (fun n : ℕ => 4 * C_step * Real.exp (-(n : ℝ))) atTop (𝓝 0) := by
    have ht : Tendsto (fun n : ℕ => Real.exp (-(n : ℝ))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop
    simpa using ht.const_mul (4 * C_step)
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1
    (hexp_lim (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)))
  let k₀ : ℕ := max 9 n₀
  have hk₀9 : 9 ≤ k₀ := le_max_left 9 n₀
  have hbk₀ : (4 * C_step) * Real.exp (-(k₀ : ℝ)) ≤ 1 / 2 := by
    simpa [mul_assoc] using hn₀ k₀ (le_max_right 9 n₀)
  obtain ⟨c₀_step, hc₀_step_14, hstep_k₀⟩ := hstep k₀ hk₀9
  obtain ⟨c₁_quant, hc₁_quant, hquant⟩ := hankel_quantC1_of_feasible
  obtain ⟨c_rinf, hc_rinf⟩ := eventually_atTop.1 hankelRinf_c43_small
  let c_poly : ℝ := (360000 * r_min_base) ^ 3
  let c₀ : ℝ := max (max c₀_step c₁_quant) (max c_rinf (max c_poly 1e14))
  have hc₀_14 : 1e14 ≤ c₀ :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  let C_half_dyad : ℝ := 2 * (C_step * (2 + (k₀ : ℝ)))
  have hC_half_pos : 0 < C_half_dyad := by dsimp [C_half_dyad]; positivity
  refine ⟨2 * C_half_dyad, r_min_base, c₀, by positivity, hr_min_base, hc₀_14, ?_⟩
  intro c ε T R_J f hc hf hε hmass hT hRJ_lb hRJ_ub hRJ_good
  have hc_step : c₀_step ≤ c := ((le_max_left _ _).trans (le_max_left _ _)).trans hc
  have hc_quant : c₁_quant ≤ c := ((le_max_right _ _).trans (le_max_left _ _)).trans hc
  have hc_rinf' : c_rinf ≤ c := ((le_max_left _ _).trans (le_max_right _ _)).trans hc
  have hc_poly : c_poly ≤ c :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hc
  have hc14 : 1e14 ≤ c := hc₀_14.trans hc
  have hc0 : 0 < c := by linarith
  have hc3 : 3e6 ≤ c := by linarith
  have hlog32 : 32 ≤ Real.log c := halfMoment_log_ge_32 hc14
  have hlog0 : 0 < Real.log c := by linarith
  have hfe := hf.toIsHankelEigenfn
  obtain ⟨u_T, ha1, huA_ub, hT_eq, hB2⟩ := hquant c ε T f hc_quant hf hε hmass hT
  obtain ⟨hu0, hu3⟩ := hankelBoot_uT_range ha1 hB2
  have huA : |u_T| ≤ langerRadius c := hankelBoot_abs_uT hc3 hu0 hu3
  -- `r_min ≤ R_J` from `Real.log c ≤ 6 c^{1/6}`
  let r_min : ℝ := r_min_base * (Real.log c) ^ 2
  have hr_min_256 : 256 ≤ r_min := by
    have : 256 * (32 : ℝ) ^ 2 ≤ r_min_base * (Real.log c) ^ 2 := by gcongr
    linarith
  have hr_min_100 : r_min ≤ (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) := by
    have hlog_bd : Real.log c ≤ 6 * c ^ (1 / 6 : ℝ) := by
      have := Real.log_le_rpow_div hc0.le (by norm_num : (0 : ℝ) < 1 / 6)
      linarith only [this]
    have hlog_sq : (Real.log c) ^ 2 ≤ 36 * c ^ (1 / 3 : ℝ) := by
      have h1 : (Real.log c) ^ 2 ≤ (6 * c ^ (1 / 6 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ hlog0.le hlog_bd 2
      have h2 : (c ^ (1 / 6 : ℝ)) ^ 2 = c ^ (1 / 3 : ℝ) := by
        rw [← Real.rpow_natCast (c ^ (1 / 6 : ℝ)) 2, ← Real.rpow_mul hc0.le]; norm_num
      calc (Real.log c) ^ 2 ≤ (6 * c ^ (1 / 6 : ℝ)) ^ 2 := h1
        _ = 36 * (c ^ (1 / 6 : ℝ)) ^ 2 := by ring
        _ = 36 * c ^ (1 / 3 : ℝ) := by rw [h2]
    have hc13 : 360000 * r_min_base ≤ c ^ (1 / 3 : ℝ) := by
      have h1 : ((360000 * r_min_base) ^ 3 : ℝ) ^ (1 / 3 : ℝ) ≤ c ^ (1 / 3 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hc_poly (by norm_num)
      have h2 : ((360000 * r_min_base) ^ (3 : ℕ) : ℝ) ^ (1 / 3 : ℝ) = 360000 * r_min_base := by
        rw [← Real.rpow_natCast _ 3, ← Real.rpow_mul (by positivity)]
        norm_num
      linarith only [h1, h2]
    have hc23 : c ^ (1 / 3 : ℝ) * c ^ (1 / 3 : ℝ) = c ^ (2 / 3 : ℝ) := by
      rw [← Real.rpow_add hc0]; norm_num
    have hprod : 360000 * r_min_base * c ^ (1 / 3 : ℝ) ≤ c ^ (2 / 3 : ℝ) := by
      have h1 := mul_le_mul_of_nonneg_right hc13 (Real.rpow_nonneg hc0.le (1 / 3 : ℝ))
      linarith only [h1, hc23]
    calc r_min = r_min_base * (Real.log c) ^ 2 := rfl
      _ ≤ r_min_base * (36 * c ^ (1 / 3 : ℝ)) := by gcongr
      _ ≤ (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) := by linarith only [hprod]
  have hr_min_RJ : r_min ≤ R_J := hr_min_100.trans hRJ_lb
  -- Radius facts at `R_J`
  have h48_RJ : 48 ≤ (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) := by linarith only [hr_min_256, hr_min_100]
  obtain ⟨hRJ_48, hRJ_A, _, hRJ_c⟩ := hankelBoot_radius_facts hc3 h48_RJ hRJ_lb hRJ_ub
  have hRJA : R_J ≤ langerRadius c := by linarith only [hRJ_A]
  have hrinf_bd : c ^ (4 / 3 : ℝ) * hankelRinf c ≤ 1 := hc_rinf c hc_rinf'
  have hrinf_nn : 0 ≤ hankelRinf c := hankelRinf_nonneg (by linarith) hfe hε hmass
  have hrinf_le : hankelRinf c ≤ c ^ (-(4 / 3 : ℝ)) := by
    have hpos : 0 < c ^ (4 / 3 : ℝ) := Real.rpow_pos_of_pos hc0 _
    calc hankelRinf c = (c ^ (4 / 3 : ℝ))⁻¹ * (c ^ (4 / 3 : ℝ) * hankelRinf c) := by
          rw [← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]
      _ ≤ (c ^ (4 / 3 : ℝ))⁻¹ * 1 := mul_le_mul_of_nonneg_left hrinf_bd (by positivity)
      _ = c ^ (-(4 / 3 : ℝ)) := by rw [mul_one, Real.rpow_neg hc0.le]
  have hsmall_rinf : ∀ r : ℝ, r ≤ R_J → (2 * langerRadius c + 2 * r) * hankelRinf c ≤ 1 := by
    intro r hr_RJ
    have hr_c : r ≤ c := (hr_RJ.trans hRJ_c).trans (by
      have h := Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ c) (by norm_num : (2 / 3 : ℝ) ≤ 1)
      simpa using h)
    have hA_c : langerRadius c ≤ 7 / 2 * R_J := (hankelBoot_radius_facts hc3 h48_RJ hRJ_lb hRJ_ub).2.2.1
    have hAc' : langerRadius c ≤ 7 / 2 * c := by
      have : R_J ≤ c := hRJ_c.trans (by
        have h := Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ c) (by norm_num : (2 / 3 : ℝ) ≤ 1)
        simpa using h)
      linarith
    have hsum_le : 2 * langerRadius c + 2 * r ≤ 9 * c := by linarith
    have hcc : c * c ^ (-(4 / 3 : ℝ)) = c ^ (-(1 / 3 : ℝ)) := by
      nth_rw 1 [← Real.rpow_one c]; rw [← Real.rpow_add hc0]; norm_num
    have h9c : 9 * c ^ (-(1 / 3 : ℝ)) ≤ 1 := by
      have hc13 : (9 : ℝ) ≤ c ^ (1 / 3 : ℝ) := by
        have h1 : (9 : ℝ) ^ 3 ≤ c := by linarith
        have h2 := Real.rpow_le_rpow (by positivity) h1 (by norm_num : (0 : ℝ) ≤ 1 / 3)
        have h3 : ((9 : ℝ) ^ (3 : ℕ)) ^ (1 / 3 : ℝ) = 9 := by
          rw [← Real.rpow_natCast (9 : ℝ) 3, ← Real.rpow_mul (by norm_num)]; norm_num
        linarith only [h2, h3]
      rw [Real.rpow_neg hc0.le, mul_inv_le_iff₀ (Real.rpow_pos_of_pos hc0 _)]
      linarith only [hc13]
    calc (2 * langerRadius c + 2 * r) * hankelRinf c
        ≤ (9 * c) * c ^ (-(4 / 3 : ℝ)) := mul_le_mul hsum_le hrinf_le hrinf_nn (by positivity)
      _ = 9 * c ^ (-(1 / 3 : ℝ)) := by rw [mul_assoc, hcc]
      _ ≤ 1 := h9c
  -- Define `S` and `L_max`
  let S : Set ℝ := {r : ℝ | r_min ≤ r ∧ r ≤ R_J ∧ ctGoodRadius r}
  let val : ℝ → ℝ := fun r => r ^ (1 / 2 : ℝ) * (hankelBootB1 c f r u_T + hankelBootB2 c f r)
  have hS_ne : (val '' S).Nonempty := ⟨val R_J, R_J, ⟨hr_min_RJ, le_rfl, hRJ_good⟩, rfl⟩
  have h_val_nn : ∀ r ∈ S, 0 ≤ val r := fun r ⟨hr_min, hr_RJ, _⟩ => by
    have hr0 : 0 < r := lt_of_lt_of_le (by linarith) hr_min
    have hru : -r ≤ u_T := by linarith
    have hrA : r ≤ langerRadius c := hr_RJ.trans hRJA
    exact mul_nonneg (Real.rpow_nonneg hr0.le _)
      (add_nonneg (hankelBootB1_nonneg hc3 hf hε hmass hT_eq hu0 hu3 hr0 hru hrA)
        (hankelBootB2_nonneg c f r))
  have hS_bdd : BddAbove (val '' S) := by
    refine ⟨3 * R_J ^ (1 / 2 : ℝ), ?_⟩
    rintro y ⟨r, ⟨hr_min, hr_RJ, _⟩, rfl⟩
    have hr0 : 0 < r := lt_of_lt_of_le (by linarith) hr_min
    have hru : -r ≤ u_T := by linarith
    have hrA : r ≤ langerRadius c := hr_RJ.trans hRJA
    have hB1_le := (hankelBootB1_le_B1k hc3 hf hε hmass hT_eq hu0 hu3 hr0 hru hrA k₀).trans
      (hankelBootB1k_le_two hc3 hf hε hmass hu0 hu3 hru hrA hr0 (hsmall_rinf r hr_RJ) k₀)
    have hB2_le : hankelBootB2 c f r ≤ 1 := hankelBootB2_le_one hc0 hfe hmass r
    have hr12 : r ^ (1 / 2 : ℝ) ≤ R_J ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow hr0.le hr_RJ (by norm_num)
    calc r ^ (1 / 2 : ℝ) * (hankelBootB1 c f r u_T + hankelBootB2 c f r)
        ≤ R_J ^ (1 / 2 : ℝ) * (2 + 1) :=
          mul_le_mul hr12 (by linarith) (add_nonneg
            (hankelBootB1_nonneg hc3 hf hε hmass hT_eq hu0 hu3 hr0 hru hrA)
            (hankelBootB2_nonneg c f r)) (Real.rpow_nonneg (by linarith) _)
      _ = 3 * R_J ^ (1 / 2 : ℝ) := by ring
  let L_max : ℝ := sSup (val '' S)
  have hL_nn : 0 ≤ L_max := by
    exact le_trans (h_val_nn R_J ⟨hr_min_RJ, le_rfl, hRJ_good⟩)
      (le_csSup hS_bdd ⟨R_J, ⟨hr_min_RJ, le_rfl, hRJ_good⟩, rfl⟩)
  -- Bound `hankelScaleL ≤ 1 + 4 * L_max` for every `r ∈ S`
  have hL_bound : ∀ r ∈ S, hankelScaleL c R_J r u_T f ≤ 1 + 4 * L_max := by
    intro r ⟨hr_min, hr_RJ, hr_good⟩
    have hr0 : 0 < r := lt_of_lt_of_le (by linarith) hr_min
    have hru : -r ≤ u_T := by linarith
    have hrA : r ≤ langerRadius c := hr_RJ.trans hRJA
    have hRJ0 : 0 < R_J := lt_of_lt_of_le hr0 hr_RJ
    have hRJu : -R_J ≤ u_T := by linarith
    have hmem_r : val r ≤ L_max := le_csSup hS_bdd ⟨r, ⟨hr_min, hr_RJ, hr_good⟩, rfl⟩
    have hmem_RJ : val R_J ≤ L_max := le_csSup hS_bdd ⟨R_J, ⟨hr_min_RJ, le_rfl, hRJ_good⟩, rfl⟩
    have ht1 : r ^ (1 / 2 : ℝ) * hankelBootB2 c f r ≤ L_max := by
      have hB1_0 := hankelBootB1_nonneg hc3 hf hε hmass hT_eq hu0 hu3 hr0 hru hrA
      have : r ^ (1 / 2 : ℝ) * hankelBootB2 c f r ≤ val r := by
        dsimp [val]; nlinarith [Real.rpow_nonneg hr0.le (1 / 2 : ℝ)]
      exact this.trans hmem_r
    have ht3 : R_J ^ (1 / 2 : ℝ) * hankelBootB2 c f R_J ≤ L_max := by
      have hB1_0 := hankelBootB1_nonneg hc3 hf hε hmass hT_eq hu0 hu3 hRJ0 hRJu hRJA
      have : R_J ^ (1 / 2 : ℝ) * hankelBootB2 c f R_J ≤ val R_J := by
        dsimp [val]; nlinarith [Real.rpow_nonneg hRJ0.le (1 / 2 : ℝ)]
      exact this.trans hmem_RJ
    let r_til : ℝ := min (1028 * r) R_J
    have hrt_lo : r_min ≤ r_til := le_min (by linarith) hr_min_RJ
    have hrt_RJ : r_til ≤ R_J := min_le_right _ _
    have hrt_256 : 256 ≤ r_til := by linarith
    have ht2 : r_til ^ (1 / 2 : ℝ) * hankelBootB1 c f r_til u_T ≤ 2 * L_max := by
      by_cases hnear : R_J - 1 ≤ r_til
      · exact (hankelScale_snap_B1 hc3 hf hε hmass hT_eq hu0 hu3 huA (by linarith only [hrt_256]) hrt_RJ
          (by linarith only [hnear]) hRJA hL_nn hmem_RJ).1
      · push Not at hnear
        obtain ⟨r', hr'_lo, hr'_hi, hr'_good⟩ :=
          hankelBoot_good_circle_window r_til (by linarith only [hrt_256])
        have hr'S : r' ∈ S := ⟨by linarith only [hrt_lo, hr'_lo], by linarith only [hr'_hi, hnear], hr'_good⟩
        have hr'A : r' ≤ langerRadius c := hr'S.2.1.trans hRJA
        exact (hankelScale_snap_B1 hc3 hf hε hmass hT_eq hu0 hu3 huA (by linarith only [hrt_256]) hr'_lo
          hr'_hi hr'A hL_nn (le_csSup hS_bdd ⟨r', hr'S, rfl⟩)).1
    have h_add : 1 + r ^ (1 / 2 : ℝ) * hankelBootB2 c f r +
        r_til ^ (1 / 2 : ℝ) * hankelBootB1 c f r_til u_T +
        R_J ^ (1 / 2 : ℝ) * hankelBootB2 c f R_J ≤ 1 + L_max + 2 * L_max + L_max :=
      add_le_add (add_le_add (add_le_add le_rfl ht1) ht2) ht3
    rw [hankelScaleL]
    linarith only [h_add]
  -- Apply `hstep_k₀` on every `r ∈ S` and absorb via `absorb_half`
  have hL_csSup : L_max ≤ C_step * (2 + (k₀ : ℝ)) + (4 * C_step) * Real.exp (-(k₀ : ℝ)) * L_max := by
    refine csSup_le hS_ne ?_
    rintro y ⟨r, hrS, rfl⟩
    have hr0 : 0 < r := lt_of_lt_of_le (by linarith) hrS.1
    have hms := hstep_k₀ c ε T u_T R_J r f hc_step hf hε hmass hT_eq ha1 hB2 hRJ_lb hRJ_ub
      hrS.1 hrS.2.1 hrS.2.2
    have hL_r := hL_bound r hrS
    have hexp_le : Real.exp (-(k₀ : ℝ)) ≤ 1 :=
      Real.exp_le_one_iff.2 (by exact neg_nonpos.2 (Nat.cast_nonneg k₀))
    have hinner : 1 + (k₀ : ℝ) + Real.exp (-(k₀ : ℝ)) * hankelScaleL c R_J r u_T f ≤
        (2 + (k₀ : ℝ)) + 4 * Real.exp (-(k₀ : ℝ)) * L_max := by
      have h1 : Real.exp (-(k₀ : ℝ)) * hankelScaleL c R_J r u_T f ≤
          Real.exp (-(k₀ : ℝ)) * (1 + 4 * L_max) :=
        mul_le_mul_of_nonneg_left hL_r (Real.exp_pos _).le
      linarith only [h1, hexp_le]
    have hmult : hankelBootB1 c f r u_T + hankelBootB2 c f r ≤
        (C_step * (2 + (k₀ : ℝ)) + (4 * C_step) * Real.exp (-(k₀ : ℝ)) * L_max) *
          r ^ (-(1 / 2 : ℝ)) := by
      have h1 : C_step * (1 + (k₀ : ℝ) + Real.exp (-(k₀ : ℝ)) * hankelScaleL c R_J r u_T f) ≤
          C_step * (2 + (k₀ : ℝ)) + (4 * C_step) * Real.exp (-(k₀ : ℝ)) * L_max :=
        (mul_le_mul_of_nonneg_left hinner hC_step_pos.le).trans_eq (by ring)
      exact hms.trans (mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hr0.le _))
    have hr12_mul : r ^ (1 / 2 : ℝ) * r ^ (-(1 / 2 : ℝ)) = 1 := by
      rw [← Real.rpow_add hr0]; norm_num
    calc r ^ (1 / 2 : ℝ) * (hankelBootB1 c f r u_T + hankelBootB2 c f r)
        ≤ r ^ (1 / 2 : ℝ) *
            ((C_step * (2 + (k₀ : ℝ)) + (4 * C_step) * Real.exp (-(k₀ : ℝ)) * L_max) *
              r ^ (-(1 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left hmult (Real.rpow_nonneg hr0.le _)
      _ = (C_step * (2 + (k₀ : ℝ)) + (4 * C_step) * Real.exp (-(k₀ : ℝ)) * L_max) *
            (r ^ (1 / 2 : ℝ) * r ^ (-(1 / 2 : ℝ))) := by ring
      _ = C_step * (2 + (k₀ : ℝ)) + (4 * C_step) * Real.exp (-(k₀ : ℝ)) * L_max := by
          rw [hr12_mul, mul_one]
  have h_abs : L_max ≤ C_half_dyad := by
    have hθL : (4 * C_step) * Real.exp (-(k₀ : ℝ)) * L_max ≤ (1 / 2 : ℝ) * L_max :=
      mul_le_mul_of_nonneg_right hbk₀ hL_nn
    dsimp [C_half_dyad]
    linarith only [hθL, hL_csSup]
  -- Now conclude `(B1 + B2 ≤ ...)` for `r ∈ S` and `B1 ≤ ...` for all `s ∈ [r_min, R_J]`.
  refine ⟨u_T, ha1, huA_ub, hT_eq, hu0, hu3, hr_min_RJ, ?_, ?_⟩
  · intro r hr_lo hr_hi hr_good
    have hr0 : 0 < r := lt_of_lt_of_le (by linarith) hr_lo
    have hpos12 : 0 < r ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hr0 _
    have hval : val r ≤ C_half_dyad := (le_csSup hS_bdd ⟨r, ⟨hr_lo, hr_hi, hr_good⟩, rfl⟩).trans h_abs
    have hC1 : C_half_dyad ≤ 2 * C_half_dyad := by linarith only [hC_half_pos]
    rw [Real.rpow_neg hr0.le]
    calc hankelBootB1 c f r u_T + hankelBootB2 c f r
        = (r ^ (1 / 2 : ℝ))⁻¹ * val r := by
          dsimp [val]; rw [← mul_assoc, inv_mul_cancel₀ hpos12.ne', one_mul]
      _ ≤ (r ^ (1 / 2 : ℝ))⁻¹ * C_half_dyad := mul_le_mul_of_nonneg_left hval (by positivity)
      _ ≤ (r ^ (1 / 2 : ℝ))⁻¹ * (2 * C_half_dyad) := mul_le_mul_of_nonneg_left hC1 (by positivity)
      _ = (2 * C_half_dyad) * (r ^ (1 / 2 : ℝ))⁻¹ := by ring
  · intro s hs_lo hs_hi
    by_cases hnear : R_J - 1 ≤ s
    · have hval : val R_J ≤ C_half_dyad :=
        (le_csSup hS_bdd ⟨R_J, ⟨hr_min_RJ, le_rfl, hRJ_good⟩, rfl⟩).trans h_abs
      exact (hankelScale_snap_B1 hc3 hf hε hmass hT_eq hu0 hu3 huA (by linarith only [hs_lo, hr_min_256]) hs_hi
        (by linarith only [hnear]) hRJA hC_half_pos.le hval).2
    · push Not at hnear
      obtain ⟨r', hr'_lo, hr'_hi, hr'_good⟩ :=
        hankelBoot_good_circle_window s (by linarith only [hs_lo, hr_min_256])
      have hr'S : r' ∈ S := ⟨by linarith only [hs_lo, hr'_lo], by linarith only [hr'_hi, hnear], hr'_good⟩
      have hr'A : r' ≤ langerRadius c := hr'S.2.1.trans hRJA
      have hval : val r' ≤ C_half_dyad := (le_csSup hS_bdd ⟨r', hr'S, rfl⟩).trans h_abs
      exact (hankelScale_snap_B1 hc3 hf hε hmass hT_eq hu0 hu3 huA (by linarith only [hs_lo, hr_min_256]) hr'_lo
        hr'_hi hr'A hC_half_pos.le hval).2

private lemma hankel_dyadic_blocks_le {c ε T u_T R_J r_min C_dyad : ℝ} {f : ℝ → ℝ}
    (hc0 : 0 < c) (hf : IsHankelFeasible c ε T f) (hT : c * hankelXi c u_T = T)
    (hu0 : u_T ≤ 0) (huA : |u_T| ≤ langerRadius c)
    (hr_min1 : 1 ≤ r_min) (hr_min_RJ : r_min ≤ R_J) (hRJA : R_J ≤ langerRadius c)
    (hru_min : -r_min ≤ u_T)
    (hC_dyad : 0 ≤ C_dyad)
    (hB1_bd : ∀ s : ℝ, r_min ≤ s → s ≤ R_J → hankelBootB1 c f s u_T ≤ C_dyad * s ^ (-(1 / 2 : ℝ))) :
    ∀ m : ℕ, ∫ v in r_min..min ((2 : ℝ) ^ m * r_min) R_J,
      (1 + v) ^ (1 / 2 : ℝ) * hankelPsiLead c f (-v) ≤ (m : ℝ) * (2 * C_dyad) := by
  have hfe := hf.toIsHankelEigenfn
  have huA_abs := abs_le.1 huA
  have hQc : ContinuousOn (fun v : ℝ => (1 + v) ^ (1 / 2 : ℝ) * hankelPsiLead c f (-v))
      (Icc 0 (langerRadius c)) := by
    have h1 : ContinuousOn (fun v : ℝ => (1 + v) ^ (1 / 2 : ℝ)) (Icc 0 (langerRadius c)) :=
      (continuousOn_const.add continuousOn_id).rpow_const fun v hv => by
        left; dsimp; linarith [hv.1]
    exact h1.mul ((continuousOn_hankelQ hc0 hfe).comp continuousOn_neg fun v hv => by
      constructor <;> linarith [hv.1, hv.2])
  intro m
  induction m with
  | zero =>
    have hmin : min ((2 : ℝ) ^ 0 * r_min) R_J = r_min := by
      simp [min_eq_left hr_min_RJ]
    rw [hmin, intervalIntegral.integral_same]
    simp
  | succ m ih =>
    set a : ℝ := min ((2 : ℝ) ^ m * r_min) R_J
    set b : ℝ := min ((2 : ℝ) ^ (m + 1) * r_min) R_J
    have hr_le_2m : r_min ≤ (2 : ℝ) ^ m * r_min :=
      le_mul_of_one_le_left (by linarith) (by exact_mod_cast Nat.one_le_two_pow)
    have ha_lo : r_min ≤ a := le_min hr_le_2m hr_min_RJ
    have ha_hi : a ≤ R_J := min_le_right _ _
    have hab : a ≤ b := min_le_min (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num) (Nat.le_succ m)) (by linarith)) le_rfl
    have hb_hi : b ≤ R_J := min_le_right _ _
    have ia : IntervalIntegrable (fun v : ℝ => (1 + v) ^ (1 / 2 : ℝ) * hankelPsiLead c f (-v))
        volume r_min a :=
      (hQc.mono (Icc_subset_Icc (by linarith) (ha_hi.trans hRJA))).intervalIntegrable_of_Icc
        (μ := volume) ha_lo
    have ib : IntervalIntegrable (fun v : ℝ => (1 + v) ^ (1 / 2 : ℝ) * hankelPsiLead c f (-v))
        volume a b :=
      (hQc.mono (Icc_subset_Icc (by linarith) (hb_hi.trans hRJA))).intervalIntegrable_of_Icc
        (μ := volume) hab
    rw [← intervalIntegral.integral_add_adjacent_intervals ia ib]
    have h_step_le : ∫ v in a..b, (1 + v) ^ (1 / 2 : ℝ) * hankelPsiLead c f (-v) ≤ 2 * C_dyad := by
      by_cases haR : R_J ≤ a
      · have hab_eq : a = b := le_antisymm hab (haR.trans' hb_hi)
        rw [hab_eq, intervalIntegral.integral_same]
        linarith only [hC_dyad]
      · push Not at haR
        have ha_eq : a = (2 : ℝ) ^ m * r_min := by
          rcases min_cases ((2 : ℝ) ^ m * r_min) R_J with ⟨h, _⟩ | ⟨h, _⟩
          · exact h
          · exact absurd (show a = R_J from h) (ne_of_lt haR)
        have ha1 : 1 ≤ a := by linarith
        have ha0 : 0 < a := by linarith
        have hb0 : 0 < b := by linarith
        have hb2a : b ≤ 2 * a := by
          calc b ≤ (2 : ℝ) ^ (m + 1) * r_min := min_le_left _ _
            _ = 2 * ((2 : ℝ) ^ m * r_min) := by rw [pow_succ']; ring
            _ = 2 * a := by rw [ha_eq]
        have h_int_lin : IntervalIntegrable (fun v : ℝ => (√2 / √a) * (v * hankelPsiLead c f (-v)))
            volume a b := by
          have hc_q : ContinuousOn (fun v : ℝ => v * hankelPsiLead c f (-v)) (Icc a b) :=
            continuousOn_id.mul ((continuousOn_hankelQ hc0 hfe).comp continuousOn_neg fun v hv => by
              constructor <;> linarith [hv.1, hv.2, hb_hi, hRJA])
          exact (continuousOn_const.mul hc_q).intervalIntegrable_of_Icc (μ := volume) hab
        have h_mono : ∫ v in a..b, (1 + v) ^ (1 / 2 : ℝ) * hankelPsiLead c f (-v) ≤
            ∫ v in a..b, (√2 / √a) * (v * hankelPsiLead c f (-v)) := by
          refine intervalIntegral.integral_mono_on hab ib h_int_lin fun v hv => ?_
          have hv1 : 1 ≤ v := ha1.trans hv.1
          have hv0 : 0 < v := by linarith
          have hvA : |-v| ≤ langerRadius c := by
            rw [abs_neg, abs_of_pos hv0]; exact hv.2.trans (hb_hi.trans hRJA)
          have hQ0 : 0 ≤ hankelPsiLead c f (-v) :=
            hankelBoot_psiLead_nonneg hc0 hf hT huA hvA (by linarith [hv.1, ha_lo, hru_min])
          have h1v : (1 + v) ^ (1 / 2 : ℝ) ≤ √2 * √v := by
            have h1 : 1 + v ≤ 2 * v := by linarith
            calc (1 + v) ^ (1 / 2 : ℝ) ≤ (2 * v) ^ (1 / 2 : ℝ) :=
                  Real.rpow_le_rpow (by linarith) h1 (by norm_num)
              _ = 2 ^ (1 / 2 : ℝ) * v ^ (1 / 2 : ℝ) := Real.mul_rpow (by norm_num) hv0.le
              _ = √2 * √v := by rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
          have hsq : √v ≤ v / √a := by
            rw [le_div_iff₀ (Real.sqrt_pos.2 ha0)]
            calc √v * √a ≤ √v * √v := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hv.1) (Real.sqrt_nonneg _)
              _ = v := Real.mul_self_sqrt hv0.le
          have h_coef : (1 + v) ^ (1 / 2 : ℝ) ≤ (√2 / √a) * v := by
            calc (1 + v) ^ (1 / 2 : ℝ) ≤ √2 * √v := h1v
              _ ≤ √2 * (v / √a) := mul_le_mul_of_nonneg_left hsq (Real.sqrt_nonneg _)
              _ = (√2 / √a) * v := by ring
          calc (1 + v) ^ (1 / 2 : ℝ) * hankelPsiLead c f (-v)
              ≤ ((√2 / √a) * v) * hankelPsiLead c f (-v) := mul_le_mul_of_nonneg_right h_coef hQ0
            _ = (√2 / √a) * (v * hankelPsiLead c f (-v)) := by ring
        have h_subst : ∫ v in a..b, v * hankelPsiLead c f (-v) =
            ∫ u in (-b)..(-a), (-u) * hankelPsiLead c f u := by
          have hcomp := intervalIntegral.integral_comp_neg (fun u : ℝ => (-u) * hankelPsiLead c f u)
            (a := a) (b := b)
          simpa using hcomp
        have h_le_bB1 : ∫ u in (-b)..(-a), (-u) * hankelPsiLead c f u ≤
            b * hankelBootB1 c f b u_T := by
          have hbA : b ≤ langerRadius c := hb_hi.trans hRJA
          have hbu : -b ≤ u_T := by linarith
          rw [hankelBoot_R_mul_B1 hc0 hf hT huA hbA hb0 hbu]
          have hQcont : ContinuousOn (fun u : ℝ => (-u) * hankelPsiLead c f u)
              (Icc (-langerRadius c) (langerRadius c)) :=
            (continuousOn_id.neg).mul (continuousOn_hankelQ hc0 hfe)
          have j1 : IntervalIntegrable (fun u : ℝ => (-u) * hankelPsiLead c f u) volume (-b) (-a) :=
            (hQcont.mono (Icc_subset_Icc (by linarith) (by linarith))).intervalIntegrable_of_Icc
              (μ := volume) (by linarith)
          have j2 : IntervalIntegrable (fun u : ℝ => (-u) * hankelPsiLead c f u) volume (-a) u_T :=
            (hQcont.mono (Icc_subset_Icc (by linarith) huA_abs.2)).intervalIntegrable_of_Icc
              (μ := volume) (by linarith)
          rw [← intervalIntegral.integral_add_adjacent_intervals j1 j2]
          have hnn : 0 ≤ ∫ u in (-a)..u_T, (-u) * hankelPsiLead c f u := by
            refine intervalIntegral.integral_nonneg (by linarith) fun u hu => ?_
            have huA' : |u| ≤ langerRadius c := by
              rw [abs_le]; constructor <;> linarith [hu.1, hu.2, huA_abs.1, huA_abs.2]
            exact mul_nonneg (by linarith [hu.2, hu0])
              (hankelBoot_psiLead_nonneg hc0 hf hT huA huA' hu.2)
          linarith only [hnn]
        have hB1_b : b * hankelBootB1 c f b u_T ≤ C_dyad * √b := by
          have h1 := hB1_bd b (ha_lo.trans hab) hb_hi
          have h2 : b * hankelBootB1 c f b u_T ≤ b * (C_dyad * b ^ (-(1 / 2 : ℝ))) :=
            mul_le_mul_of_nonneg_left h1 hb0.le
          have hb_mul : b * b ^ (-(1 / 2 : ℝ)) = √b := by
            have hsq : √b * √b = b := Real.mul_self_sqrt hb0.le
            rw [Real.rpow_neg hb0.le, ← Real.sqrt_eq_rpow]
            calc b * (√b)⁻¹ = (√b * √b) * (√b)⁻¹ := by rw [hsq]
              _ = √b * (√b * (√b)⁻¹) := by ring
              _ = √b * 1 := by rw [mul_inv_cancel₀ (Real.sqrt_pos.2 hb0).ne']
              _ = √b := mul_one _
          calc b * hankelBootB1 c f b u_T ≤ b * (C_dyad * b ^ (-(1 / 2 : ℝ))) := h2
            _ = C_dyad * (b * b ^ (-(1 / 2 : ℝ))) := by ring
            _ = C_dyad * √b := by rw [hb_mul]
        calc ∫ v in a..b, (1 + v) ^ (1 / 2 : ℝ) * hankelPsiLead c f (-v)
            ≤ ∫ v in a..b, (√2 / √a) * (v * hankelPsiLead c f (-v)) := h_mono
          _ = (√2 / √a) * ∫ v in a..b, v * hankelPsiLead c f (-v) :=
              intervalIntegral.integral_const_mul _ _
          _ = (√2 / √a) * ∫ u in (-b)..(-a), (-u) * hankelPsiLead c f u := by rw [h_subst]
          _ ≤ (√2 / √a) * (b * hankelBootB1 c f b u_T) :=
              mul_le_mul_of_nonneg_left h_le_bB1 (by positivity)
          _ ≤ (√2 / √a) * (C_dyad * √b) :=
              mul_le_mul_of_nonneg_left hB1_b (by positivity)
          _ ≤ (√2 / √a) * (C_dyad * (√2 * √a)) := by
              have hrb : √b ≤ √2 * √a := by
                calc √b ≤ √(2 * a) := Real.sqrt_le_sqrt hb2a
                  _ = √2 * √a := Real.sqrt_mul (by norm_num) _
              gcongr
          _ = C_dyad * (√2 * √2) * (√a / √a) := by ring
          _ = 2 * C_dyad := by
              rw [Real.mul_self_sqrt (by norm_num), div_self (Real.sqrt_pos.2 ha0).ne', mul_one]; ring
    calc (∫ v in r_min..a, (1 + v) ^ (1 / 2 : ℝ) * hankelPsiLead c f (-v)) +
          ∫ v in a..b, (1 + v) ^ (1 / 2 : ℝ) * hankelPsiLead c f (-v)
        ≤ (m : ℝ) * (2 * C_dyad) + 2 * C_dyad := add_le_add ih h_step_le
      _ = ((m + 1 : ℕ) : ℝ) * (2 * C_dyad) := by push_cast; ring

/-- **Negative first half-moment (`constant_terms_lower.tex`, `ct:half` (1))**:
there exist constants `C_half > 0` and `c₀ ≥ 1e14` such that for every `c ≥ c₀`,
every feasible normalized Hankel eigenfunction `(f, T)` with `T < cξ(a₁)`,
and every `R' ∈ [0, 10⁻⁴ c^{2/3}]`,
`∫ v in Set.Ioo 0 R', (1 + v)^{1/2} |Re Ψ̃(-v)| dv ≤ C_half * log c`. -/
theorem hankel_neg_half_moment_le :
    ∃ C_half c₀ : ℝ, 0 < C_half ∧ 1e14 ≤ c₀ ∧
      ∀ (c ε T R' : ℝ) (f : ℝ → ℝ), c₀ ≤ c →
        IsHankelFeasible c ε T f → (ε = 1 ∨ ε = -1) → hankelMass c f = 1 →
        T < c * hankelXi c (airyZero 1) →
        0 ≤ R' → R' ≤ (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) →
        ∫ v in Set.Ioo (0 : ℝ) R', (1 + v) ^ (1 / 2 : ℝ) * |hankelPsiR c f (-v)| ≤
          C_half * Real.log c := by
  obtain ⟨C_dyad, r_min_base, c₀_dy, hC_dyad_pos, hr_min_base, hc₀_dy_14, hdyadic⟩ :=
    hankel_scale_dyadic_bound
  obtain ⟨c_rinf, hc_rinf⟩ := eventually_atTop.1 hankelRinf_c43_small
  let C_half : ℝ := 2 * Real.sqrt (2 * r_min_base) + 6 * C_dyad + 1
  have hC_half_pos : 0 < C_half := by dsimp [C_half]; positivity
  let c₀ : ℝ := max c₀_dy (max c_rinf (max 1e14 8))
  refine ⟨C_half, c₀, hC_half_pos, (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)), ?_⟩
  intro c ε T R' f hc hf hε hmass hT hR'_0 hR'_ub
  have hc_dy : c₀_dy ≤ c := (le_max_left _ _).trans hc
  have hc_rinf' : c_rinf ≤ c := ((le_max_left _ _).trans (le_max_right _ _)).trans hc
  have hc14 : 1e14 ≤ c := ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hc
  have hc0 : 0 < c := by linarith
  have hc3 : 3e6 ≤ c := by linarith
  have hc5 : 5000 ≤ c := by linarith
  have hlog32 : 32 ≤ Real.log c := halfMoment_log_ge_32 hc14
  have hlog0 : 0 < Real.log c := by linarith
  have hc23_ge : 1e8 ≤ c ^ (2 / 3 : ℝ) := by
    have h1 : (1e12 : ℝ) ^ (2 / 3 : ℝ) ≤ c ^ (2 / 3 : ℝ) :=
      Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
    have h2 : (1e12 : ℝ) ^ (2 / 3 : ℝ) = 1e8 := by
      have h3 : (1e12 : ℝ) = (1e4 : ℝ) ^ (3 : ℕ) := by norm_num
      rw [h3, ← Real.rpow_natCast (1e4 : ℝ) 3, ← Real.rpow_mul (by norm_num)]; norm_num
    linarith
  have h48_RJ : 48 ≤ (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) := by linarith
  obtain ⟨R_J, hRJ1, hRJ2, hRJ_good⟩ :=
    hankelBoot_good_circle_window ((1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ)) (by linarith)
  have hR'_RJ : R' ≤ R_J := hR'_ub.trans hRJ1
  obtain ⟨u_T, ha1, huA_ub, hT_eq, hu0, hu3, hr_min_RJ, _, hB1_bd⟩ :=
    hdyadic c ε T R_J f hc_dy hf hε hmass hT hRJ1 hRJ2 hRJ_good
  have huA : |u_T| ≤ langerRadius c := hankelBoot_abs_uT hc3 hu0 hu3
  obtain ⟨hRJ_48, hRJ_A, hA_RJ, hRJ_c⟩ := hankelBoot_radius_facts hc3 h48_RJ hRJ1 hRJ2
  have hRJA : R_J ≤ langerRadius c := by linarith only [hRJ_A]
  have hfe := hf.toIsHankelEigenfn
  let r_min : ℝ := r_min_base * (Real.log c) ^ 2
  have hr_min_256 : 256 ≤ r_min := by
    have : 256 * (32 : ℝ) ^ 2 ≤ r_min_base * (Real.log c) ^ 2 := by gcongr
    linarith
  have hr_min1 : 1 ≤ r_min := by linarith
  have hr_min_A : r_min ≤ langerRadius c := hr_min_RJ.trans hRJA
  have hru_min : -r_min ≤ u_T := by linarith
  let g : ℝ → ℝ := fun v => (1 + v) ^ (1 / 2 : ℝ) * |hankelPsiR c f (-v)|
  have hg_cont : ContinuousOn g (Icc 0 (langerRadius c)) := by
    refine (ContinuousOn.rpow_const (continuousOn_const.add continuousOn_id)
      (fun v hv => Or.inl (by dsimp; linarith [hv.1]))).mul ?_
    exact (continuousOn_hankelPsiR hc0 hfe).abs.comp continuousOn_neg fun v hv => by
      constructor <;> linarith [hv.1, hv.2]
  have hg_nn : ∀ v : ℝ, 0 ≤ v → 0 ≤ g v := fun v hv =>
    mul_nonneg (Real.rpow_nonneg (by linarith) _) (abs_nonneg _)
  have ig_0R' : IntervalIntegrable g volume 0 R' :=
    (hg_cont.mono (Icc_subset_Icc le_rfl (hR'_RJ.trans hRJA))).intervalIntegrable_of_Icc
      (μ := volume) hR'_0
  have ig_R'RJ : IntervalIntegrable g volume R' R_J :=
    (hg_cont.mono (Icc_subset_Icc hR'_0 hRJA)).intervalIntegrable_of_Icc (μ := volume) hR'_RJ
  have ig_0rmin : IntervalIntegrable g volume 0 r_min :=
    (hg_cont.mono (Icc_subset_Icc le_rfl hr_min_A)).intervalIntegrable_of_Icc
      (μ := volume) (by linarith)
  have ig_rminRJ : IntervalIntegrable g volume r_min R_J :=
    (hg_cont.mono (Icc_subset_Icc (by linarith) hRJA)).intervalIntegrable_of_Icc
      (μ := volume) hr_min_RJ
  have h_to_0RJ : ∫ v in Set.Ioo (0 : ℝ) R', g v ≤
      (∫ v in (0 : ℝ)..r_min, g v) + ∫ v in r_min..R_J, g v := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hR'_0]
    have hnn_tail : 0 ≤ ∫ v in R'..R_J, g v :=
      intervalIntegral.integral_nonneg hR'_RJ fun v hv => hg_nn v (hR'_0.trans hv.1)
    have hsum1 : (∫ v in (0 : ℝ)..R', g v) + ∫ v in R'..R_J, g v = ∫ v in (0 : ℝ)..R_J, g v :=
      intervalIntegral.integral_add_adjacent_intervals ig_0R' ig_R'RJ
    have hsum2 : (∫ v in (0 : ℝ)..r_min, g v) + ∫ v in r_min..R_J, g v = ∫ v in (0 : ℝ)..R_J, g v :=
      intervalIntegral.integral_add_adjacent_intervals ig_0rmin ig_rminRJ
    linarith only [hnn_tail, hsum1, hsum2]
  -- Bound on `rinf`
  have hrinf_bd : c ^ (4 / 3 : ℝ) * hankelRinf c ≤ 1 := hc_rinf c hc_rinf'
  have hrinf_nn : 0 ≤ hankelRinf c := hankelRinf_nonneg (by linarith) hfe hε hmass
  have hrinf_le : hankelRinf c ≤ c ^ (-(4 / 3 : ℝ)) := by
    have hpos : 0 < c ^ (4 / 3 : ℝ) := Real.rpow_pos_of_pos hc0 _
    calc hankelRinf c = (c ^ (4 / 3 : ℝ))⁻¹ * (c ^ (4 / 3 : ℝ) * hankelRinf c) := by
          rw [← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]
      _ ≤ (c ^ (4 / 3 : ℝ))⁻¹ * 1 := mul_le_mul_of_nonneg_left hrinf_bd (by positivity)
      _ = c ^ (-(4 / 3 : ℝ)) := by rw [mul_one, Real.rpow_neg hc0.le]
  have hRJ_c_le : R_J ≤ c := hRJ_c.trans (by
    have h := Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ c) (by norm_num : (2 / 3 : ℝ) ≤ 1)
    simpa using h)
  have h2Arinf : 2 * langerRadius c * hankelRinf c ≤ 1 := by
    have hsum : 2 * langerRadius c ≤ 7 * c := by linarith
    have hcc : c * c ^ (-(4 / 3 : ℝ)) = c ^ (-(1 / 3 : ℝ)) := by
      nth_rw 1 [← Real.rpow_one c]; rw [← Real.rpow_add hc0]; norm_num
    have h7c : 7 * c ^ (-(1 / 3 : ℝ)) ≤ 1 := by
      have hc13 : (7 : ℝ) ≤ c ^ (1 / 3 : ℝ) := by
        have h1 : (7 : ℝ) ^ 3 ≤ c := by linarith
        have h2 := Real.rpow_le_rpow (by positivity) h1 (by norm_num : (0 : ℝ) ≤ 1 / 3)
        have h3 : ((7 : ℝ) ^ (3 : ℕ)) ^ (1 / 3 : ℝ) = 7 := by
          rw [← Real.rpow_natCast (7 : ℝ) 3, ← Real.rpow_mul (by norm_num)]; norm_num
        linarith only [h2, h3]
      rw [Real.rpow_neg hc0.le, mul_inv_le_iff₀ (Real.rpow_pos_of_pos hc0 _)]
      linarith only [hc13]
    calc 2 * langerRadius c * hankelRinf c ≤ (7 * c) * c ^ (-(4 / 3 : ℝ)) :=
          mul_le_mul hsum hrinf_le hrinf_nn (by positivity)
      _ = 7 * c ^ (-(1 / 3 : ℝ)) := by rw [mul_assoc, hcc]
      _ ≤ 1 := h7c
  -- Piece 1: `[0, r_min]`
  have h_piece1 : ∫ v in (0 : ℝ)..r_min, g v ≤ 2 * Real.sqrt (2 * r_min_base) * Real.log c := by
    let C_w : ℝ := Real.sqrt (2 * r_min_base) * Real.log c
    have hCw_nn : 0 ≤ C_w := by dsimp [C_w]; positivity
    have h_abs_cont : ContinuousOn (fun v : ℝ => |hankelPsiR c f (-v)|) (Icc 0 r_min) :=
      (continuousOn_hankelPsiR hc0 hfe).abs.comp continuousOn_neg fun v hv => by
        constructor <;> linarith [hv.1, hv.2, hr_min_A]
    have i_abs : IntervalIntegrable (fun v : ℝ => |hankelPsiR c f (-v)|) volume 0 r_min :=
      h_abs_cont.intervalIntegrable_of_Icc (μ := volume) (by linarith)
    have h_mono : ∫ v in (0 : ℝ)..r_min, g v ≤ ∫ v in (0 : ℝ)..r_min, C_w * |hankelPsiR c f (-v)| := by
      refine intervalIntegral.integral_mono_on (by linarith) ig_0rmin (i_abs.const_mul C_w) fun v hv => ?_
      have hw : (1 + v) ^ (1 / 2 : ℝ) ≤ C_w := by
        have h1v : 1 + v ≤ 2 * r_min := by linarith [hv.2]
        have h2r : Real.sqrt (2 * r_min) = C_w := by
          dsimp [C_w, r_min]
          rw [show 2 * (r_min_base * (Real.log c) ^ 2) = (2 * r_min_base) * (Real.log c) ^ 2 by ring,
            Real.sqrt_mul (by positivity), Real.sqrt_sq hlog0.le]
        rw [← Real.sqrt_eq_rpow]
        calc Real.sqrt (1 + v) ≤ Real.sqrt (2 * r_min) := Real.sqrt_le_sqrt h1v
          _ = C_w := h2r
      exact mul_le_mul_of_nonneg_right hw (abs_nonneg _)
    have h_mass_neg : ∫ v in (0 : ℝ)..r_min, |hankelPsiR c f (-v)| ≤ 2 := by
      have h_sub : ∫ v in (0 : ℝ)..r_min, |hankelPsiR c f (-v)| =
          ∫ u in (-r_min)..0, |hankelPsiR c f u| := by
        simpa using intervalIntegral.integral_comp_neg (fun u : ℝ => |hankelPsiR c f u|)
          (a := (0 : ℝ)) (b := r_min)
      have hA_pos : 0 < langerRadius c := langerRadius_pos hc0
      have hc_abs : ContinuousOn (fun u : ℝ => |hankelPsiR c f u|)
          (Icc (-langerRadius c) (langerRadius c)) := (continuousOn_hankelPsiR hc0 hfe).abs
      have i1 : IntervalIntegrable (fun u : ℝ => |hankelPsiR c f u|) volume (-langerRadius c) (-r_min) :=
        (hc_abs.mono (Icc_subset_Icc le_rfl (by linarith))).intervalIntegrable_of_Icc
          (μ := volume) (by linarith)
      have i2 : IntervalIntegrable (fun u : ℝ => |hankelPsiR c f u|) volume (-r_min) 0 :=
        (hc_abs.mono (Icc_subset_Icc (by linarith) hA_pos.le)).intervalIntegrable_of_Icc
          (μ := volume) (by linarith)
      have i3 : IntervalIntegrable (fun u : ℝ => |hankelPsiR c f u|) volume 0 (langerRadius c) :=
        (hc_abs.mono (Icc_subset_Icc (by linarith) le_rfl)).intervalIntegrable_of_Icc
          (μ := volume) hA_pos.le
      have h12 := intervalIntegral.integral_add_adjacent_intervals i1 i2
      have h123 := intervalIntegral.integral_add_adjacent_intervals (i1.trans i2) i3
      have hn1 : 0 ≤ ∫ u in (-langerRadius c)..(-r_min), |hankelPsiR c f u| :=
        intervalIntegral.integral_nonneg (by linarith) fun _ _ => abs_nonneg _
      have hn3 : 0 ≤ ∫ u in (0 : ℝ)..(langerRadius c), |hankelPsiR c f u| :=
        intervalIntegral.integral_nonneg hA_pos.le fun _ _ => abs_nonneg _
      have htot := hankel_psi_abs_mass hc5 hfe hε hmass
      linarith only [h_sub, h12, h123, hn1, hn3, htot, h2Arinf]
    calc ∫ v in (0 : ℝ)..r_min, g v
        ≤ ∫ v in (0 : ℝ)..r_min, C_w * |hankelPsiR c f (-v)| := h_mono
      _ = C_w * ∫ v in (0 : ℝ)..r_min, |hankelPsiR c f (-v)| := intervalIntegral.integral_const_mul _ _
      _ ≤ C_w * 2 := mul_le_mul_of_nonneg_left h_mass_neg hCw_nn
      _ = 2 * Real.sqrt (2 * r_min_base) * Real.log c := by dsimp [C_w]; ring
  -- Piece 2: `[r_min, R_J]`
  have h_piece2 : ∫ v in r_min..R_J, g v ≤ (6 * C_dyad + 1) * Real.log c := by
    let err_c : ℝ := (1 + R_J) ^ (1 / 2 : ℝ) * hankelRinf c
    let lead_w : ℝ → ℝ := fun v => (1 + v) ^ (1 / 2 : ℝ) * hankelPsiLead c f (-v)
    have h_lead_cont : ContinuousOn lead_w (Icc r_min R_J) := by
      refine (ContinuousOn.rpow_const (continuousOn_const.add continuousOn_id)
        (fun v hv => Or.inl (by dsimp; linarith [hv.1]))).mul ?_
      exact (continuousOn_hankelQ hc0 hfe).comp continuousOn_neg fun v hv => by
        constructor <;> linarith [hv.1, hv.2, hRJA]
    have i_lead : IntervalIntegrable lead_w volume r_min R_J :=
      h_lead_cont.intervalIntegrable_of_Icc (μ := volume) hr_min_RJ
    have i_rhs : IntervalIntegrable (fun v : ℝ => lead_w v + err_c) volume r_min R_J :=
      i_lead.add intervalIntegrable_const
    have h_split_pt : ∫ v in r_min..R_J, g v ≤
        ∫ v in r_min..R_J, (lead_w v + err_c) := by
      refine intervalIntegral.integral_mono_on hr_min_RJ ig_rminRJ i_rhs fun v hv => ?_
      have hv0 : 0 < v := by linarith [hv.1]
      have hvA : |-v| ≤ langerRadius c := by
        rw [abs_neg, abs_of_pos hv0]; exact hv.2.trans hRJA
      have hQ0 : 0 ≤ hankelPsiLead c f (-v) :=
        hankelBoot_psiLead_nonneg hc0 hf hT_eq huA hvA (by linarith [hv.1, hru_min])
      have hdiff := hankelPsiR_sub_Q_le hc5 hfe hε hmass hvA
      have habs : |hankelPsiR c f (-v)| ≤ hankelPsiLead c f (-v) + hankelRinf c := by
        have h1 : |hankelPsiR c f (-v)| ≤
            |hankelPsiLead c f (-v)| + |hankelPsiR c f (-v) - hankelPsiLead c f (-v)| := by
          calc |hankelPsiR c f (-v)|
              = |hankelPsiLead c f (-v) + (hankelPsiR c f (-v) - hankelPsiLead c f (-v))| := by
                ring_nf
            _ ≤ |hankelPsiLead c f (-v)| + |hankelPsiR c f (-v) - hankelPsiLead c f (-v)| :=
                abs_add_le _ _
        rw [abs_of_nonneg hQ0] at h1
        linarith only [h1, hdiff]
      have hw_le : (1 + v) ^ (1 / 2 : ℝ) ≤ (1 + R_J) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow (by linarith) (by linarith [hv.2]) (by norm_num)
      have hw_nn : 0 ≤ (1 + v) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by linarith) _
      calc g v = (1 + v) ^ (1 / 2 : ℝ) * |hankelPsiR c f (-v)| := rfl
        _ ≤ (1 + v) ^ (1 / 2 : ℝ) * (hankelPsiLead c f (-v) + hankelRinf c) :=
            mul_le_mul_of_nonneg_left habs hw_nn
        _ = lead_w v + (1 + v) ^ (1 / 2 : ℝ) * hankelRinf c := by dsimp [lead_w]; ring
        _ ≤ lead_w v + err_c :=
            add_le_add le_rfl (mul_le_mul_of_nonneg_right hw_le hrinf_nn)
    rw [intervalIntegral.integral_add i_lead intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul] at h_split_pt
    let M : ℕ := 2 * (Nat.floor (Real.log c) + 1)
    have hM_cov : R_J ≤ (2 : ℝ) ^ M * r_min := by
      have hlog_lt : Real.log c ≤ (Nat.floor (Real.log c) + 1 : ℕ) := by
        exact_mod_cast (Nat.lt_floor_add_one (Real.log c)).le
      have hexp_le : c ≤ (4 : ℝ) ^ (Nat.floor (Real.log c) + 1) := by
        have h1 : Real.exp 1 ≤ 4 := by linarith [Real.exp_one_lt_d9]
        calc c = Real.exp (Real.log c) := (Real.exp_log hc0).symm
          _ ≤ Real.exp ((Nat.floor (Real.log c) + 1 : ℕ) : ℝ) := Real.exp_le_exp.2 hlog_lt
          _ = (Real.exp 1) ^ (Nat.floor (Real.log c) + 1) := by
              rw [← Real.exp_nat_mul, mul_one]
          _ ≤ (4 : ℝ) ^ (Nat.floor (Real.log c) + 1) :=
              pow_le_pow_left₀ (Real.exp_pos 1).le h1 _
      have h4_eq : (4 : ℝ) ^ (Nat.floor (Real.log c) + 1) = (2 : ℝ) ^ M := by
        dsimp [M]; rw [pow_mul]; norm_num
      have hc_le_2M : c ≤ (2 : ℝ) ^ M := h4_eq ▸ hexp_le
      calc R_J ≤ c := hRJ_c_le
        _ ≤ (2 : ℝ) ^ M := hc_le_2M
        _ ≤ (2 : ℝ) ^ M * r_min := le_mul_of_one_le_right (by positivity) hr_min1
    have hM_le_3log : (M : ℝ) ≤ 3 * Real.log c := by
      have hfl : (Nat.floor (Real.log c) : ℝ) ≤ Real.log c := Nat.floor_le hlog0.le
      have hM_cast : (M : ℝ) = 2 * ((Nat.floor (Real.log c) : ℝ) + 1) := by
        dsimp [M]; push_cast; ring
      linarith only [hM_cast, hfl, hlog32]
    have h_dy := hankel_dyadic_blocks_le hc0 hf hT_eq hu0 huA hr_min1 hr_min_RJ hRJA hru_min
      hC_dyad_pos.le hB1_bd M
    rw [min_eq_right hM_cov] at h_dy
    have h_lead_bd : ∫ v in r_min..R_J, lead_w v ≤ 6 * C_dyad * Real.log c := by
      calc ∫ v in r_min..R_J, lead_w v ≤ (M : ℝ) * (2 * C_dyad) := h_dy
        _ ≤ (3 * Real.log c) * (2 * C_dyad) :=
            mul_le_mul_of_nonneg_right hM_le_3log (by positivity)
        _ = 6 * C_dyad * Real.log c := by ring
    have h_err_bd : (R_J - r_min) * err_c ≤ Real.log c := by
      have h1RJ : 1 + R_J ≤ c ^ (2 / 3 : ℝ) := by linarith
      have hw_RJ : (1 + R_J) ^ (1 / 2 : ℝ) ≤ c ^ (1 / 3 : ℝ) := by
        calc (1 + R_J) ^ (1 / 2 : ℝ) ≤ (c ^ (2 / 3 : ℝ)) ^ (1 / 2 : ℝ) :=
              Real.rpow_le_rpow (by linarith) h1RJ (by norm_num)
          _ = c ^ (1 / 3 : ℝ) := by rw [← Real.rpow_mul hc0.le]; norm_num
      have h_prod : R_J * (1 + R_J) ^ (1 / 2 : ℝ) ≤ c := by
        have hcc : c ^ (2 / 3 : ℝ) * c ^ (1 / 3 : ℝ) = c := by
          rw [← Real.rpow_add hc0]; norm_num
        calc R_J * (1 + R_J) ^ (1 / 2 : ℝ) ≤ c ^ (2 / 3 : ℝ) * c ^ (1 / 3 : ℝ) :=
              mul_le_mul hRJ_c hw_RJ (Real.rpow_nonneg (by linarith) _) (by positivity)
          _ = c := hcc
      have herr_nn : 0 ≤ err_c :=
        mul_nonneg (Real.rpow_nonneg (by linarith) _) hrinf_nn
      have hc13_le1 : c * c ^ (-(4 / 3 : ℝ)) ≤ 1 := by
        have h1 : c * c ^ (-(4 / 3 : ℝ)) = c ^ (-(1 / 3 : ℝ)) := by
          nth_rw 1 [← Real.rpow_one c]; rw [← Real.rpow_add hc0]; norm_num
        have hc1 : (1 : ℝ) ≤ c := by linarith
        have h2 : c ^ (-(1 / 3 : ℝ)) ≤ (1 : ℝ) ^ (-(1 / 3 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos (by norm_num) hc1 (by norm_num)
        simpa [h1] using h2
      calc (R_J - r_min) * err_c ≤ R_J * err_c :=
            mul_le_mul_of_nonneg_right (by linarith) herr_nn
        _ = (R_J * (1 + R_J) ^ (1 / 2 : ℝ)) * hankelRinf c := by dsimp [err_c]; ring
        _ ≤ c * c ^ (-(4 / 3 : ℝ)) :=
            mul_le_mul h_prod hrinf_le hrinf_nn hc0.le
        _ ≤ 1 := hc13_le1
        _ ≤ Real.log c := by linarith only [hlog32]
    linarith only [h_split_pt, h_lead_bd, h_err_bd]
  calc ∫ v in Set.Ioo (0 : ℝ) R', g v
      ≤ (∫ v in (0 : ℝ)..r_min, g v) + ∫ v in r_min..R_J, g v := h_to_0RJ
    _ ≤ 2 * Real.sqrt (2 * r_min_base) * Real.log c + (6 * C_dyad + 1) * Real.log c :=
        add_le_add h_piece1 h_piece2
    _ = C_half * Real.log c := by dsimp [C_half]; ring

/-- info: 'FormalResearch.SignUncertainty.hankel_scale_dyadic_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankel_scale_dyadic_bound

/-- info: 'FormalResearch.SignUncertainty.hankel_neg_half_moment_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankel_neg_half_moment_le

end FormalResearch.SignUncertainty
