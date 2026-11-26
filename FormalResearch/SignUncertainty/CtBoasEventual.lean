module

public import Mathlib
public import FormalResearch.SignUncertainty.CtBoasFinal
public import FormalResearch.SignUncertainty.CtBoasRegime

/-!
# `ct:boas-ineq`: the regime `c ≥ c₀`

The numerical regime facts of `boas_concrete_core` (largeness of `c` against the fixed constants `c₁`, `κ₀`, `C_θ`), each as an
eventual statement about `c`, and their conjunction (`boas_regime`).  **Proved**, unconditional.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

/-- `c^s ≥ M` for large `c`, `s > 0`. -/
lemma ev_rpow_ge {s : ℝ} (hs : 0 < s) (M : ℝ) : ∀ᶠ c : ℝ in atTop, M ≤ c ^ s :=
  (tendsto_rpow_atTop hs).eventually_ge_atTop M

lemma ev_exp_neg : ∀ᶠ c : ℝ in atTop, Real.exp (-c) ≤ (c ^ 12)⁻¹ := by
  filter_upwards [eventually_rpow_mul_exp_le 12 1 one_pos, eventually_gt_atTop (0 : ℝ)] with c h hc
  have e : c ^ (12 : ℝ) = c ^ 12 := by norm_num
  rw [e, one_mul] at h
  rw [← one_div, le_div_iff₀ (by positivity)]
  linarith [mul_comm (c ^ 12) (Real.exp (-c))]

lemma ev_hcR {c₁ : ℝ} (hc₁ : 0 < c₁) :
    ∀ᶠ c : ℝ in atTop, 2 ≤ c ^ (4 / 7 : ℝ) ∧ c ^ (4 / 7 : ℝ) + 1 / 2 ≤ c₁ ^ 2 * c ^ (2 / 3 : ℝ) := by
  filter_upwards [ev_rpow_ge (by norm_num : (0 : ℝ) < 4 / 7) 2, ev_rpow_ge (by norm_num : (0 : ℝ) < 2 / 21) (5 / (4 * c₁ ^ 2)),
    eventually_gt_atTop (0 : ℝ)] with c h1 h2 hc
  refine ⟨h1, ?_⟩
  have e : c ^ (2 / 3 : ℝ) = c ^ (4 / 7 : ℝ) * c ^ (2 / 21 : ℝ) := by
    rw [← Real.rpow_add hc]; norm_num
  rw [e]
  have h3 : 5 / 4 ≤ c₁ ^ 2 * c ^ (2 / 21 : ℝ) := by
    rw [div_le_iff₀ (by positivity)] at h2
    nlinarith
  nlinarith

lemma ev_hlo {κ₀ : ℝ} (hκ₀ : 0 < κ₀) :
    ∀ᶠ c : ℝ in atTop, c ^ (-(1 / 3) : ℝ) ≤ κ₀ * c ^ (-(2 / 21) : ℝ) := by
  filter_upwards [ev_rpow_ge (by norm_num : (0 : ℝ) < 5 / 21) (1 / κ₀), eventually_gt_atTop (0 : ℝ)] with c h hc
  have e : c ^ (-(1 / 3) : ℝ) = c ^ (-(2 / 21) : ℝ) * c ^ (-(5 / 21) : ℝ) := by
    rw [← Real.rpow_add hc]; norm_num
  have e2 : c ^ (-(5 / 21) : ℝ) = (c ^ (5 / 21 : ℝ))⁻¹ := Real.rpow_neg hc.le _
  have h5 : 0 < c ^ (5 / 21 : ℝ) := Real.rpow_pos_of_pos hc _
  have h6 : (c ^ (5 / 21 : ℝ))⁻¹ ≤ κ₀ := by
    rw [inv_le_comm₀ h5 hκ₀]
    have : 1 / κ₀ = κ₀⁻¹ := one_div _
    rwa [this] at h
  rw [e]
  have : 0 < c ^ (-(2 / 21) : ℝ) := Real.rpow_pos_of_pos hc _
  rw [e2] at *
  nlinarith

lemma ev_hLt {κ₀ : ℝ} (hκ₀ : 0 < κ₀) :
    ∀ᶠ c : ℝ in atTop, 6 / (0.998 * langerScale c) ≤ κ₀ * c ^ (-(2 / 21) : ℝ) := by
  have hκ := langerKappa_pos
  filter_upwards [ev_rpow_ge (by norm_num : (0 : ℝ) < 4 / 7) (6 / (0.998 * langerKappa * κ₀)), eventually_gt_atTop (0 : ℝ)]
    with c h hc
  have hK := langerScale_pos hc
  rw [div_le_iff₀ (by positivity)]
  have e : c ^ (-(2 / 21) : ℝ) * c ^ (2 / 3 : ℝ) = c ^ (4 / 7 : ℝ) := by
    rw [← Real.rpow_add hc]; norm_num
  have e2 : κ₀ * c ^ (-(2 / 21) : ℝ) * (0.998 * langerScale c) = 0.998 * langerKappa * κ₀ * c ^ (4 / 7 : ℝ) := by
    unfold langerScale
    rw [← e]; ring
  rw [e2]
  rw [div_le_iff₀ (by positivity)] at h
  linarith

lemma ev_hreg {κ₀ : ℝ} (hκ₀ : 0 < κ₀) :
    ∀ᶠ c : ℝ in atTop, 36000000 * Real.log c ≤ (κ₀ * c ^ (-(2 / 21) : ℝ)) ^ 3 * c := by
  filter_upwards [ev_rpow_ge (by norm_num : (0 : ℝ) < 4 / 7) (36000000 / κ₀ ^ 3), eventually_log_le_rpow (1 / 7) (by norm_num),
    eventually_gt_atTop (0 : ℝ)] with c h hl hc
  have e : (c ^ (-(2 / 21) : ℝ)) ^ 3 * c = c ^ (5 / 7 : ℝ) := by
    have h3 : (c ^ (-(2 / 21) : ℝ)) ^ 3 = c ^ (-(2 / 7) : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hc.le]; norm_num
    calc (c ^ (-(2 / 21) : ℝ)) ^ 3 * c = c ^ (-(2 / 7) : ℝ) * c ^ (1 : ℝ) := by rw [h3, Real.rpow_one]
      _ = c ^ (5 / 7 : ℝ) := by rw [← Real.rpow_add hc]; norm_num
  have e2 : c ^ (5 / 7 : ℝ) = c ^ (4 / 7 : ℝ) * c ^ (1 / 7 : ℝ) := by
    rw [← Real.rpow_add hc]; norm_num
  have h1 : 36000000 / κ₀ ^ 3 ≤ c ^ (4 / 7 : ℝ) := h
  rw [div_le_iff₀ (by positivity)] at h1
  rw [mul_pow, mul_assoc, e, e2]
  have h7 : 0 < c ^ (1 / 7 : ℝ) := Real.rpow_pos_of_pos hc _
  nlinarith [mul_le_mul_of_nonneg_right h1 h7.le]

lemma ev_hlogc : ∀ᶠ c : ℝ in atTop, Real.log (π ^ 2 * Real.log c) + 1 + 1 / 18 ≤ Real.log c := by
  filter_upwards [eventually_ge_atTop (Real.exp 21), eventually_gt_atTop (1 : ℝ)] with c hc hc1
  have hc0 : 0 < c := by linarith
  have hy : 21 ≤ Real.log c := (Real.le_log_iff_exp_le hc0).2 hc
  have hy0 : 0 < Real.log c := by linarith
  have h1 : Real.log (π ^ 2 * Real.log c) = Real.log (π ^ 2) + Real.log (Real.log c) :=
    Real.log_mul (by positivity) hy0.ne'
  have h2 : Real.log (π ^ 2) ≤ 9 := by
    have := Real.log_le_sub_one_of_pos (by positivity : 0 < π ^ 2)
    nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have h3 : Real.log (Real.log c) ≤ Real.log c / 2 := by
    have := Real.log_le_sub_one_of_pos (by positivity : 0 < Real.log c / 2)
    rw [Real.log_div hy0.ne' (by norm_num)] at this
    have := Real.log_two_lt_d9
    linarith
  linarith

lemma ev_hJb (κ₀ : ℝ) : ∀ᶠ c : ℝ in atTop, 37 * |Real.log κ₀| + 3 ≤ 20 * Real.log c := by
  filter_upwards [eventually_ge_atTop (Real.exp ((37 * |Real.log κ₀| + 3) / 20)), eventually_gt_atTop (0 : ℝ)] with c hc hc0
  have := (Real.le_log_iff_exp_le hc0).2 hc
  linarith

set_option maxHeartbeats 1000000 in
/-- **`ct:boas`** (`ct:boas-ineq` with the taper): there is `c₁₀ > 0` such that for every `c₁ ∈ (0, c₁₀]` the statement
`CtBoasStatement c₁` holds, from `boas_concrete_core` (the concrete `BoasInputs`), the top-scale moments `ct_boas_moments_top`,
the `L_min` facts `ctLv0_facts`, the taper band `taperBand_regime`, the total error `boasErrTotal_le` and the regime `ev_*`.
**Proved**, unconditional. -/
theorem ct_boas_concrete : ∃ c₁₀ : ℝ, 0 < c₁₀ ∧ ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ c₁₀ → CtBoasStatement c₁ := by
  obtain ⟨Cθ1, hCθ1⟩ := ct_outer_theta_asymp
  obtain ⟨Cθ2, hCθ20, hCθ2⟩ := ct_outer_theta_deriv_bound
  obtain ⟨K, cM, hK0, hmom⟩ := ct_boas_moments_top
  obtain ⟨κ₀, hκ₀, cL, hcL1, hL⟩ := ctLv0_facts
  obtain ⟨γ₁, hγ₁, hband₁⟩ := taperBand_regime (ε := 1) (Or.inl rfl)
  obtain ⟨γ₂, hγ₂, hband₂⟩ := taperBand_regime (ε := -1) (Or.inr rfl)
  set Cθ : ℝ := max (max Cθ1 Cθ2) 0 with hCθdef
  have hCθ0 : 0 ≤ Cθ := le_max_right _ _
  have hC1 : Cθ1 ≤ Cθ := (le_max_left _ _).trans (le_max_left _ _)
  have hC2 : Cθ2 ≤ Cθ := (le_max_right _ _).trans (le_max_left _ _)
  refine ⟨min (min γ₁ γ₂) (1 / 200), lt_min (lt_min hγ₁ hγ₂) (by norm_num), fun c₁ hc₁ hc₁le => ?_⟩
  have hc₁1 : c₁ ≤ γ₁ := (hc₁le.trans (min_le_left _ _)).trans (min_le_left _ _)
  have hc₁2 : c₁ ≤ γ₂ := (hc₁le.trans (min_le_left _ _)).trans (min_le_right _ _)
  have hc₁3 : c₁ ≤ 1 / 200 := hc₁le.trans (min_le_right _ _)
  obtain ⟨cB₁, hcB₁, hB₁⟩ := hband₁ c₁ hc₁ hc₁1
  obtain ⟨cB₂, hcB₂, hB₂⟩ := hband₂ c₁ hc₁ hc₁2
  obtain ⟨C₀, hC₀, hErr⟩ := boasErrTotal_le Cθ hCθ0 hc₁ hK0 hκ₀
  obtain ⟨c0F, -, hF⟩ := regime_large
  have hev : ∀ᶠ c : ℝ in atTop, cM ≤ c ∧ cL ≤ c ∧ cB₁ ≤ c ∧ cB₂ ≤ c ∧
      max (Real.exp 7) (max 1 (84000 ^ 2 / κ₀)) ≤ c ∧ c0F ≤ c ∧
      Real.exp (-c) ≤ (c ^ 12)⁻¹ ∧ (2 ≤ c ^ (4 / 7 : ℝ) ∧ c ^ (4 / 7 : ℝ) + 1 / 2 ≤ c₁ ^ 2 * c ^ (2 / 3 : ℝ)) ∧
      c ^ (-(1 / 3) : ℝ) ≤ κ₀ * c ^ (-(2 / 21) : ℝ) ∧ 6 / (0.998 * langerScale c) ≤ κ₀ * c ^ (-(2 / 21) : ℝ) ∧
      36000000 * Real.log c ≤ (κ₀ * c ^ (-(2 / 21) : ℝ)) ^ 3 * c ∧
      Real.log (π ^ 2 * Real.log c) + 1 + 1 / 18 ≤ Real.log c ∧ 37 * |Real.log κ₀| + 3 ≤ 20 * Real.log c ∧
      boasFarEps c ⌈c ^ 2⌉₊ (boasPhaseEps c Cθ) ≤ 60 * c ^ (-(2 : ℝ)) ∧
      boasErrTotal c₁ K Cθ κ₀ c ≤ C₀ * (c ^ (-(4 / 3) : ℝ) * Real.log c) := by
    filter_upwards [eventually_ge_atTop cM, eventually_ge_atTop cL, eventually_ge_atTop cB₁, eventually_ge_atTop cB₂,
      eventually_ge_atTop (max (Real.exp 7) (max 1 (84000 ^ 2 / κ₀))), eventually_ge_atTop c0F, ev_exp_neg, ev_hcR hc₁,
      ev_hlo hκ₀, ev_hLt hκ₀, ev_hreg hκ₀, ev_hlogc, ev_hJb κ₀, eventually_farEps_le Cθ, hErr] with c h1 h2 h3 h4 h5 h6 h7 h8 h9
      h10 h11 h12 h13 h14 h15
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩
  obtain ⟨c₀, hc₀⟩ := eventually_atTop.1 hev
  refine ⟨C₀, c₀, fun c hc ε hε T f hf hmass hT _hgap R hR _hgood => ?_⟩
  obtain ⟨hcM, hcL, hcB₁, hcB₂, hcs, hc0F, hexp, ⟨hc47, hcR⟩, hlo, hLt, hreg, hlogc, hJb, hfar, hErr'⟩ := hc₀ c hc
  have hc7 : Real.exp 7 ≤ c := (le_max_left _ _).trans hcs
  have hc0 : 0 < c := lt_of_lt_of_le (Real.exp_pos 7) hc7
  have hc1 : 1 < c := lt_of_lt_of_le (by linarith [Real.add_one_le_exp (7 : ℝ)]) hc7
  have hlog7 : 7 ≤ Real.log c := (Real.le_log_iff_exp_le hc0).2 hc7
  have hB : TaperBand ε c R := by
    rcases hε with rfl | rfl
    · exact hB₁ c hcB₁ R hR.1 hR.2
    · exact hB₂ c hcB₂ R hR.1 hR.2
  have hRhi : R ≤ (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) := by
    have h23 : 0 < c ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hc0 _
    have : 4 * c₁ ^ 2 ≤ (1 / 100 : ℝ) ^ 2 := by nlinarith
    nlinarith [hR.2]
  have hR1 : 1 ≤ c₁ ^ 2 * c ^ (2 / 3 : ℝ) := by linarith
  obtain ⟨LJ, Lt, -, hLJe, hLJv, -, hLt0, hLtLJ, hLte, hLtv, hLT, hTπ, hMom, hTail⟩ := hmom c ε T f hcM hf hε hmass hT
  obtain ⟨hL0, hLe, hLv, hLκ⟩ := hL c hcL
  obtain ⟨hF1, hF2⟩ := hF c hc0F
  have hfE : farE2 c ≤ 2 * c ^ (-(2 : ℝ)) := farE2_le hc1 (by linarith)
  have hθa : ∀ τ : ℝ, 1 ≤ τ → |CtOuter.outerTheta ε τ + (3 + ε) * π / 4| ≤ Cθ * ((1 + τ ^ 2) * Real.exp (-π * τ)) := by
    intro τ hτ
    refine (hCθ1 ε hε.symm τ hτ).trans (mul_le_mul_of_nonneg_right hC1 (by positivity))
  have hθb : ∀ t : ℝ, |deriv (CtOuter.outerTheta ε) t| ≤ Cθ / (1 + |t|) ^ 2 := by
    intro t
    exact (hCθ2 ε hε.symm t).trans (div_le_div_of_nonneg_right hC2 (by positivity))
  have key := boas_concrete_core (K := K) (c₁ := c₁) (κ₀ := κ₀) hCθ0 hθa hθb hc₁ hK0 hκ₀ hε hf hmass hB hR.1 hRhi hLJe hLJv
    hLt0 hLtLJ hLte hLtv hLT hTπ hMom hTail hL0 hLe hLv hLκ hcs hF1 hF2 hexp hc47 hcR hR1 hlo hLt hreg hlogc hJb hfar hfE
  linarith

/-- info: 'FormalResearch.SignUncertainty.ct_boas_concrete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ct_boas_concrete

end FormalResearch.SignUncertainty
