module

public import FormalResearch.SignUncertainty.CeLiftTailNeg
public import FormalResearch.SignUncertainty.CeHankelPairFromEigen

/-!
# Proof of `CeShiftedLift` (`thm:ce-shifted-lift`)

Discharges `CeShiftedLift` (`ce_shifted_witnesses.tex`, `thm:ce-shifted-lift`) at Hankel level:
for every compact `S ⊆ ℝ`, cutoff `u_* : ℝ`, and `H₀` with `IsAiryLiftSeed S u_* H₀`,
there exist `K₀ > 0`, `ρ₁ > 0`, and `d₀ : ℕ` such that for all `d ≥ d₀`, `G = (fp + fm) / 2`
provides the positive-transform, negative-tail, negative-shell-window Hankel pair.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.Special

private lemma neg_ray_of_lift_seed {S : Set ℝ} {u_star : ℝ} {H₀ : ℂ → ℂ}
    (hseed : IsAiryLiftSeed S u_star H₀) :
    ∃ R_t c₀ : ℝ, 0 < c₀ ∧ ∀ x : ℝ, R_t ≤ x →
      c₀ * (1 + x) ^ (-(3 / 2 : ℝ)) ≤ -(H₀ ((-x : ℝ) : ℂ)).re := by
  rcases hseed.2.2.2.1 with ⟨c₀, hc₀, h1⟩ | ⟨_, _, _, c₀, hc₀, h2⟩
  · refine ⟨max (-u_star) 0, c₀, hc₀, fun x hx => ?_⟩
    have hu : -x ≤ u_star := by linarith [le_max_left (-u_star) 0]
    have hle := h1 (-x) hu
    have hx0 : 0 ≤ x := (le_max_right (-u_star) 0).trans hx
    rwa [abs_neg, abs_of_nonneg hx0] at hle
  · exact ⟨|u_star| + 1, c₀, hc₀, h2⟩

private lemma airyBetaInf_neg_of_tail {H₀ : ℂ → ℂ} {β₀₀ β₁₁ : ℝ}
    (hF_base : HasGenRationalAiryCoeffs H₀ β₀₀ β₁₁)
    {R_t c₀ : ℝ} (hc₀ : 0 < c₀)
    (htail : ∀ x : ℝ, R_t ≤ x → c₀ * (1 + x) ^ (-(3 / 2 : ℝ)) ≤ -(H₀ ((-x : ℝ) : ℂ)).re) :
    airyBetaInf H₀ < 0 := by
  obtain ⟨R₀, K_w, hR5, hK_w, hwkb⟩ := hF_base.neg_axis_wkb
  let η : ℝ := Real.pi * c₀ / (4 * (2 : ℝ) ^ (3 / 2 : ℝ))
  have hη : 0 < η := by positivity
  let R_big : ℝ := max (max R₀ R_t) 1
  let A : ℝ := max R_big ((2 * K_w / η + 1) ^ 2)
  have hA1 : 1 ≤ A := (le_max_right _ _).trans (le_max_left _ _)
  have hk_bd : ∀ {x : ℝ}, A ≤ x → K_w * x ^ (-(1 / 2 : ℝ)) ≤ η / 2 := fun {x} hx => by
    have hx0 : 0 < x := by linarith
    have hx_sq : (2 * K_w / η + 1) ^ 2 ≤ x := (le_max_right _ _).trans hx
    have hsqrt : 2 * K_w / η + 1 ≤ √x := by
      rw [← Real.sqrt_sq (by positivity : 0 ≤ 2 * K_w / η + 1)]
      exact Real.sqrt_le_sqrt hx_sq
    have hx12 : x ^ (-(1 / 2 : ℝ)) = 1 / √x := by
      rw [Real.sqrt_eq_rpow, Real.rpow_neg hx0.le, ← one_div]
    rw [hx12]
    have hsqrt_pos : 0 < √x := Real.sqrt_pos.mpr hx0
    calc K_w * (1 / √x) = K_w / √x := by ring
      _ ≤ K_w / (2 * K_w / η + 1) := by
          rcases eq_or_lt_of_le hK_w with h0 | hpos
          · simp [← h0]
          · exact div_le_div_of_nonneg_left hK_w (by positivity) hsqrt
      _ ≤ η / 2 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith [mul_nonneg hK_w hη.le, div_mul_cancel₀ (2 * K_w) hη.ne']
  have hneg_bd : ∀ {x : ℝ}, A ≤ x →
      Real.pi * x ^ (3 / 2 : ℝ) * (H₀ ((-x : ℝ) : ℂ)).re ≤ -(4 * η) := fun {x} hx => by
    have hx1 : 1 ≤ x := hA1.trans hx
    have hx0 : 0 < x := by linarith
    have hRt : R_t ≤ x := (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hx))
    have ht1 : (H₀ ((-x : ℝ) : ℂ)).re ≤ -c₀ * (1 + x) ^ (-(3 / 2 : ℝ)) := by
      linarith [htail x hRt]
    have h1x : 1 + x ≤ 2 * x := by linarith
    have hrpow : (2 * x) ^ (-(3 / 2 : ℝ)) ≤ (1 + x) ^ (-(3 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) h1x (by norm_num)
    have h2x_eq : (2 * x) ^ (-(3 / 2 : ℝ)) = (2 : ℝ) ^ (-(3 / 2 : ℝ)) * x ^ (-(3 / 2 : ℝ)) :=
      Real.mul_rpow (by norm_num) hx0.le
    have hx32_inv : x ^ (3 / 2 : ℝ) * x ^ (-(3 / 2 : ℝ)) = 1 := by
      rw [← Real.rpow_add hx0, show (3 / 2 : ℝ) + -(3 / 2 : ℝ) = 0 by norm_num, Real.rpow_zero]
    have hmul := mul_le_mul_of_nonneg_left ht1 (mul_nonneg Real.pi_pos.le (Real.rpow_nonneg hx0.le (3 / 2 : ℝ)))
    calc Real.pi * x ^ (3 / 2 : ℝ) * (H₀ ((-x : ℝ) : ℂ)).re
        ≤ Real.pi * x ^ (3 / 2 : ℝ) * (-c₀ * (1 + x) ^ (-(3 / 2 : ℝ))) := hmul
      _ = -(Real.pi * c₀ * (x ^ (3 / 2 : ℝ) * (1 + x) ^ (-(3 / 2 : ℝ)))) := by ring
      _ ≤ -(Real.pi * c₀ * (x ^ (3 / 2 : ℝ) * ((2 : ℝ) ^ (-(3 / 2 : ℝ)) * x ^ (-(3 / 2 : ℝ))))) :=
          neg_le_neg (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (h2x_eq ▸ hrpow) (Real.rpow_nonneg hx0.le _)) (by positivity))
      _ = -(Real.pi * c₀ * (2 : ℝ) ^ (-(3 / 2 : ℝ))) := by
          have hxr : x ^ (3 / 2 : ℝ) * ((2 : ℝ) ^ (-(3 / 2 : ℝ)) * x ^ (-(3 / 2 : ℝ))) = (2 : ℝ) ^ (-(3 / 2 : ℝ)) := by
            calc x ^ (3 / 2 : ℝ) * ((2 : ℝ) ^ (-(3 / 2 : ℝ)) * x ^ (-(3 / 2 : ℝ)))
                = (x ^ (3 / 2 : ℝ) * x ^ (-(3 / 2 : ℝ))) * (2 : ℝ) ^ (-(3 / 2 : ℝ)) := by ring
              _ = (2 : ℝ) ^ (-(3 / 2 : ℝ)) := by rw [hx32_inv, one_mul]
          rw [hxr]
      _ = -(4 * η) := by
          dsimp [η]; rw [Real.rpow_neg (by norm_num)]; ring
  let k : ℕ := ⌈(2 / 3 * A ^ (3 / 2 : ℝ) + Real.pi / 4) / Real.pi⌉₊ + 1
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
  have hkA : 2 / 3 * A ^ (3 / 2 : ℝ) + Real.pi / 4 < (k : ℝ) * Real.pi := by
    have hk_ceil := Nat.le_ceil ((2 / 3 * A ^ (3 / 2 : ℝ) + Real.pi / 4) / Real.pi)
    have hlt : (2 / 3 * A ^ (3 / 2 : ℝ) + Real.pi / 4) / Real.pi < (k : ℝ) := by
      dsimp [k]; push_cast; linarith
    exact (div_lt_iff₀ Real.pi_pos).mp hlt
  let x₁ : ℝ := ((3 / 2 : ℝ) * ((k : ℝ) * Real.pi - Real.pi / 4)) ^ (2 / 3 : ℝ)
  let x₂ : ℝ := ((3 / 2 : ℝ) * ((k : ℝ) * Real.pi + Real.pi / 4)) ^ (2 / 3 : ℝ)
  have hx₁_base : 0 ≤ (3 / 2 : ℝ) * ((k : ℝ) * Real.pi - Real.pi / 4) := by
    have : 0 ≤ 2 / 3 * A ^ (3 / 2 : ℝ) := by positivity
    linarith [hkA]
  have hx₂_base : 0 ≤ (3 / 2 : ℝ) * ((k : ℝ) * Real.pi + Real.pi / 4) := by positivity
  have hx₁_ge : A ≤ x₁ := by
    have h1 : A ^ (3 / 2 : ℝ) ≤ (3 / 2 : ℝ) * ((k : ℝ) * Real.pi - Real.pi / 4) := by linarith
    calc A = (A ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) := by rw [← Real.rpow_mul (by positivity)]; norm_num
      _ ≤ x₁ := Real.rpow_le_rpow (by positivity) h1 (by norm_num)
  have hx₂_ge : A ≤ x₂ := by
    have h1 : A ^ (3 / 2 : ℝ) ≤ (3 / 2 : ℝ) * ((k : ℝ) * Real.pi + Real.pi / 4) := by
      linarith [Real.pi_pos]
    calc A = (A ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) := by rw [← Real.rpow_mul (by positivity)]; norm_num
      _ ≤ x₂ := Real.rpow_le_rpow (by positivity) h1 (by norm_num)
  have hθ₁ : cohnTheta x₁ = (k : ℝ) * Real.pi := by
    unfold cohnTheta
    have h32 : x₁ ^ (3 / 2 : ℝ) = (3 / 2 : ℝ) * ((k : ℝ) * Real.pi - Real.pi / 4) := by
      dsimp [x₁]; rw [← Real.rpow_mul hx₁_base]; norm_num
    rw [h32]; ring
  have hθ₂ : cohnTheta x₂ = (k : ℝ) * Real.pi + Real.pi / 2 := by
    unfold cohnTheta
    have h32 : x₂ ^ (3 / 2 : ℝ) = (3 / 2 : ℝ) * ((k : ℝ) * Real.pi + Real.pi / 4) := by
      dsimp [x₂]; rw [← Real.rpow_mul hx₂_base]; norm_num
    rw [h32]; ring
  have hR₀₁ : R₀ ≤ x₁ := (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hx₁_ge))
  have hR₀₂ : R₀ ≤ x₂ := (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hx₂_ge))
  have hw₁ := hwkb x₁ hR₀₁
  have hw₂ := hwkb x₂ hR₀₂
  rw [hθ₁, Real.sin_nat_mul_pi, Real.cos_nat_mul_pi] at hw₁
  have hcos_sq : ((-1 : ℝ) ^ k) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_add, hcos_sq, mul_one] at hw₁
  rw [hθ₂, Real.sin_add_pi_div_two, Real.cos_add_pi_div_two, Real.sin_nat_mul_pi, Real.cos_nat_mul_pi] at hw₂
  simp only [neg_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero, hcos_sq, mul_one] at hw₂
  have hβ₁₁ : β₁₁ ≤ -(3 * η) := by
    linarith [(abs_sub_le_iff.mp hw₁).2, hk_bd hx₁_ge, hneg_bd hx₁_ge]
  have hβ₀₀ : β₀₀ ≤ -(3 * η) := by
    linarith [(abs_sub_le_iff.mp hw₂).2, hk_bd hx₂_ge, hneg_bd hx₂_ge]
  rw [hF_base.beta_eq.2.2.1]
  linarith

private lemma compact_neg_nbhd {S : Set ℝ} (hS : IsCompact S) {H₀ : ℂ → ℂ} (hH_diff : Differentiable ℂ H₀)
    (hS_neg : ∀ s ∈ S, (H₀ (s : ℂ)).re < 0) :
    ∃ B_t ρ₁ η₀ : ℝ, 0 ≤ B_t ∧ 0 < ρ₁ ∧ 0 < η₀ ∧
      ∀ s' : ℝ, (∃ s ∈ S, |s' - s| ≤ ρ₁) →
        |s'| ≤ B_t ∧ ∀ u : ℝ, |u - s'| ≤ ρ₁ → (H₀ (u : ℂ)).re ≤ -η₀ := by
  by_cases hne : S.Nonempty
  · have hcont : Continuous (fun u : ℝ => (H₀ (u : ℂ)).re) :=
      Complex.continuous_re.comp (hH_diff.continuous.comp Complex.continuous_ofReal)
    obtain ⟨s_max, hs_max, hs_max_prop⟩ := hS.exists_isMaxOn hne hcont.continuousOn
    have hη_S : 0 < -(H₀ (s_max : ℂ)).re := by linarith [hS_neg s_max hs_max]
    obtain ⟨B₀, hB₀_bd⟩ := hS.isBounded.subset_closedBall 0
    have hB₀_nn : 0 ≤ B₀ := by
      obtain ⟨s₀, hs₀⟩ := hne
      have := hB₀_bd hs₀
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
      exact (abs_nonneg s₀).trans this
    have hS_Icc : ∀ s ∈ S, |s| ≤ B₀ := fun s hs => by
      have := hB₀_bd hs
      simpa [Metric.mem_closedBall, Real.dist_eq, sub_zero] using this
    let M_I : Set ℝ := Icc (-(B₀ + 1)) (B₀ + 1)
    have huc : UniformContinuousOn (fun u : ℝ => (H₀ (u : ℂ)).re) M_I :=
      isCompact_Icc.uniformContinuousOn_of_continuous hcont.continuousOn
    obtain ⟨δ, hδ, hδ_unif⟩ := Metric.uniformContinuousOn_iff.mp huc (-(H₀ (s_max : ℂ)).re / 2) (half_pos hη_S)
    let ρ₁ : ℝ := min (δ / 4) (1 / 2)
    have hρ₁ : 0 < ρ₁ := lt_min (by linarith) (by norm_num)
    refine ⟨B₀ + ρ₁, ρ₁, -(H₀ (s_max : ℂ)).re / 2, by linarith, hρ₁, half_pos hη_S, fun s' ⟨s, hs, hs'⟩ => ?_⟩
    have hs_abs := hS_Icc s hs
    have hs'_abs : |s'| ≤ B₀ + ρ₁ := calc |s'| = |(s' - s) + s| := congrArg abs (by ring)
      _ ≤ |s' - s| + |s| := abs_add_le _ _
      _ ≤ ρ₁ + B₀ := add_le_add hs' hs_abs
      _ = B₀ + ρ₁ := by ring
    refine ⟨hs'_abs, fun u hu => ?_⟩
    have hus_dist : |u - s| ≤ 2 * ρ₁ := calc |u - s| = |(u - s') + (s' - s)| := congrArg abs (by ring)
      _ ≤ |u - s'| + |s' - s| := abs_add_le _ _
      _ ≤ ρ₁ + ρ₁ := add_le_add hu hs'
      _ = 2 * ρ₁ := by ring
    have hs_mem : s ∈ M_I := abs_le.mp (hs_abs.trans (by linarith))
    have hu_mem : u ∈ M_I := abs_le.mp (calc |u| = |(u - s) + s| := congrArg abs (by ring)
      _ ≤ |u - s| + |s| := abs_add_le _ _
      _ ≤ 2 * ρ₁ + B₀ := add_le_add hus_dist hs_abs
      _ ≤ 1 + B₀ := by linarith [min_le_right (δ / 4) (1 / 2)]
      _ = B₀ + 1 := by ring)
    have hdist_lt : dist u s < δ := by
      rw [Real.dist_eq]
      calc |u - s| ≤ 2 * ρ₁ := hus_dist
        _ ≤ 2 * (δ / 4) := by linarith [min_le_left (δ / 4) (1 / 2)]
        _ < δ := by linarith
    have hud := hδ_unif u hu_mem s hs_mem hdist_lt
    rw [Real.dist_eq, abs_sub_lt_iff] at hud
    have hs_le : (H₀ (s : ℂ)).re ≤ (H₀ (s_max : ℂ)).re := hs_max_prop hs
    linarith
  · refine ⟨0, 1, 1, le_rfl, one_pos, one_pos, fun s' ⟨s, hs, _⟩ => False.elim (hne ⟨s, hs⟩)⟩

/-- **Theorem `thm:ce-shifted-lift`** (`ce_shifted_witnesses.tex`): Hankel-level Cohn–Elkies pairs
from rational-Airy lift seeds `IsAiryLiftSeed S u_star H₀`. -/
theorem ce_shifted_lift_proved : CeShiftedLift := by
  intro S hS u_star H₀ hseed
  obtain ⟨hInGen, hH_mass, hS_neg, htail, hbplus, hH_lap⟩ := hseed
  obtain ⟨β₀₀, β₁₁, hF_base⟩ := hInGen
  obtain ⟨R_t, c₀_t, hc₀_t, hray⟩ := neg_ray_of_lift_seed ⟨⟨β₀₀, β₁₁, hF_base⟩, hH_mass, hS_neg, htail, hbplus, hH_lap⟩
  have hbinf : airyBetaInf H₀ < 0 := airyBetaInf_neg_of_tail hF_base hc₀_t hray
  have hX_neg_tail : ∃ c_neg > (0 : ℝ), ∃ w_neg ≤ (0 : ℝ),
      ∀ u : ℝ, u ≤ w_neg → c_neg * (1 + |u|) ^ (-(3 / 2 : ℝ)) ≤ -(H₀ (u : ℂ)).re := by
    refine ⟨c₀_t, hc₀_t, min (-R_t) 0, min_le_right _ _, fun u hu => ?_⟩
    have hx_ge : R_t ≤ -u := by linarith [hu.trans (min_le_left (-R_t) 0)]
    have hu0 : u ≤ 0 := hu.trans (min_le_right (-R_t) 0)
    have h1 := hray (-u) hx_ge
    rw [abs_of_nonpos hu0]
    simpa [neg_neg] using h1
  obtain ⟨M_α_unif, hM_α, K_post, hKp, W_of⟩ :=
    ce_twoEdge_lift_unif_of_K hF_base hH_mass hH_lap hbinf hbplus hX_neg_tail
      (p := 3 / 4) (γ := 1) (θ := 1) (lam := 1) (by norm_num) (by norm_num) one_pos one_pos one_pos
  obtain ⟨K, hKp_K, W, K₀, c_tail, hK₀, hW_ctail, htail_neg⟩ :=
    shifted_tail_neg_of_lift_seed hF_base hbinf (p := 3 / 4) (γ := 1) (θ := 1) (lam := 1)
      (by norm_num) (by norm_num) zero_le_one zero_le_one one_pos htail hM_α hKp W_of
  have hK1 : 1 ≤ K := hKp.trans hKp_K
  obtain ⟨B_t, ρ₁, η₀, hBt, hρ₁, hη₀, hcompact_nb⟩ := compact_neg_nbhd hS hF_base.1.1 hS_neg
  obtain ⟨c_win, hW_cwin, hwin_neg⟩ :=
    shifted_compact_window_neg hF_base (p := 3 / 4) (γ := 1) (θ := 1) (lam := 1)
      (by norm_num) (by norm_num) zero_le_one zero_le_one one_pos hK1 W hBt le_rfl hρ₁ hη₀
  let c_req : ℝ := max c_tail c_win
  let d₀ : ℕ := ⌈2 * c_req⌉₊ + 2
  refine ⟨K₀, ρ₁, d₀, hK₀, hρ₁, fun d hd => ?_⟩
  let c : ℝ := (d : ℝ) / 2
  have hc_tail : c_tail ≤ c := by
    have hd_r : 2 * c_req ≤ (d : ℝ) := by
      have hceil : 2 * c_req ≤ (⌈2 * c_req⌉₊ : ℝ) := Nat.le_ceil _
      have hdd : (⌈2 * c_req⌉₊ : ℝ) ≤ (d : ℝ) := by exact_mod_cast le_trans (Nat.le_add_right _ 2) hd
      linarith
    exact (le_max_left c_tail c_win).trans (by dsimp [c]; linarith)
  have hc_win : c_win ≤ c := by
    have hd_r : 2 * c_req ≤ (d : ℝ) := by
      have hceil : 2 * c_req ≤ (⌈2 * c_req⌉₊ : ℝ) := Nat.le_ceil _
      have hdd : (⌈2 * c_req⌉₊ : ℝ) ≤ (d : ℝ) := by exact_mod_cast le_trans (Nat.le_add_right _ 2) hd
      linarith
    exact (le_max_right c_tail c_win).trans (by dsimp [c]; linarith)
  have hc_min : W.c_min ≤ c := hW_ctail.trans hc_tail
  have hc2k : 2000 ≤ c := W.hc2k.trans hc_min
  have hc12 : 1 / 2 < c := by linarith
  let G : ℝ → ℝ := fun Δ => (W.fp c Δ + W.fm c Δ) / 2
  let T_ub : ℝ := max 1 (c / Real.pi ^ 2 - (u_star / hankelBeta1) * c ^ (1 / 3 : ℝ) + K₀)
  have hpair := ceHankelPair_of_eigenfns (T := T_ub) hc12 (W.hp hc_min) (W.hm hc_min)
    (W.hfm0 hc_min) (W.hfp0 hc_min) (fun Δ hΔ => by linarith [W.hhat_pos hc_min hΔ])
    (fun Δ hΔ => by
      have hT : c / Real.pi ^ 2 - (u_star / hankelBeta1) * c ^ (1 / 3 : ℝ) + K₀ ≤ Δ :=
        (le_max_right _ _).trans hΔ
      linarith [htail_neg hc_tail hT])
  refine ⟨G, hpair.1, hpair.2.1, fun Δ hΔ => ?_, hpair.2.2.2.1, hpair.2.2.2.2.1, hpair.2.2.2.2.2.1,
    fun Δ hΔ => htail_neg hc_tail hΔ, fun s' hs' hΔ_nn => ?_⟩
  · have hH_eq : besselHankelTransform c G Δ = (W.fp c Δ - W.fm c Δ) / 2 := by
      rw [besselHankelTransform_half_sum hc12 (W.hp hc_min).int (W.hm hc_min).int,
        (W.hp hc_min).eigen Δ hΔ, (W.hm hc_min).eigen Δ hΔ]
      ring
    rw [hH_eq]
    exact W.hhat_pos hc_min hΔ
  · obtain ⟨hs'_bd, hu_nb⟩ := hcompact_nb s' hs'
    have h0 : |(0 : ℝ)| ≤ 0 := by simp
    simpa only [add_zero] using (hwin_neg hc_win hs'_bd h0 hu_nb).2

/-- info: 'FormalResearch.SignUncertainty.ce_shifted_lift_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.ce_shifted_lift_proved

end FormalResearch.SignUncertainty