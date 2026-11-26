module

public import FormalResearch.SignUncertainty.UctSeedW

/-!
# `W^seed`: Hölder continuity at the corners `ζ = 0, 1` (hypothesis (M2) of `uct:admiss`) (F2a)

Source: `CFT/sign_uncertainty/paper/constant_terms_upper.tex`, `(uct:Wseed-def)`, "verifies hypotheses (M1)-(M3)".  **Proved.**

* `seedT_holder`: `|F̃_{*,δ}(iw) - F̃_{*,δ}(0)| ≤ C |w|^{1/2}` on `Re w ≥ 0` (`uct_airy_trans_small`, and boundedness);
* `seedW_oneSub`: `W^seed(1-ζ) = ε W^seed(ζ)`;
* `seedW_holder0`, `seedW_holder1`: `|W^seed(ζ) - W^seed(0)| ≤ C|ζ|^{1/2}` and `|W^seed(ζ) - W^seed(1)| ≤ C|1-ζ|^{1/2}`.
  Near `0` we have `W^seed = Q T(aζ)` on the closed strip with `Q = T(a)⁻¹ Z_ε e^{-H_0} T(a(1-ζ))` holomorphic on `D(0,1/2)`.
-/

@[expose] public section

open Complex Filter Topology Metric Set
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.SignUncertainty.CtOuter

lemma seedT_zero {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) : seedT δ 0 = -((ceK : ℂ) * δ) := by
  obtain ⟨C, hC0, hC⟩ := uct_airy_trans_small
  have h := hC δ hδ0 hδ1 0 (by simp) (by simp)
  rw [Complex.zero_cpow (by norm_num)] at h
  simp only [mul_zero, add_zero, norm_zero, Real.zero_rpow (by norm_num : (3 / 2 : ℝ) ≠ 0)] at h
  have h0 : airyTwistedLaplaceC (uctFstarDelta δ) 0 + (ceK : ℂ) * δ = 0 := by
    have := norm_nonneg (airyTwistedLaplaceC (uctFstarDelta δ) 0 + (ceK : ℂ) * δ)
    exact norm_le_zero_iff.mp (by simpa [mul_zero] using h)
  unfold seedT
  linear_combination h0

lemma rpow_three_half_le {s : ℝ} (h0 : 0 ≤ s) (h2 : s ≤ 2) : s ^ (3 / 2 : ℝ) ≤ 2 * s ^ (1 / 2 : ℝ) := by
  rcases h0.eq_or_lt with rfl | hs
  · simp
  · have : s ^ (3 / 2 : ℝ) = s * s ^ (1 / 2 : ℝ) := by
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hs, Real.rpow_one]
    rw [this]
    exact mul_le_mul_of_nonneg_right h2 (by positivity)

lemma self_le_two_rpow_half {s : ℝ} (h0 : 0 ≤ s) (h2 : s ≤ 2) : s ≤ 2 * s ^ (1 / 2 : ℝ) := by
  rcases h0.eq_or_lt with rfl | hs
  · simp
  · have h1 : s ^ (1 / 2 : ℝ) * s ^ (1 / 2 : ℝ) = s := by
      rw [← Real.rpow_add hs]; norm_num
    have h3 : s ^ (1 / 2 : ℝ) ≤ 2 := by
      have : s ^ (1 / 2 : ℝ) ≤ 2 ^ (1 / 2 : ℝ) := Real.rpow_le_rpow h0 h2 (by norm_num)
      have h4 : (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 := by
        calc (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          _ = 2 := Real.rpow_one 2
      linarith
    nlinarith [Real.rpow_nonneg h0 (1 / 2 : ℝ)]

theorem seedT_holder {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, 0 ≤ w.re → ‖seedT δ w - seedT δ 0‖ ≤ C * ‖w‖ ^ (1 / 2 : ℝ) := by
  obtain ⟨C, hC0, hC⟩ := uct_airy_trans_small
  obtain ⟨B, hB⟩ := seedT_bound δ
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0 (by simp))
  refine ⟨max (2 * C + ‖uctC‖ + 2 * (|δ| * ‖(ceK : ℂ)‖ * ‖uctA1‖)) (2 * B), by positivity, fun w hw => ?_⟩
  by_cases h2 : ‖w‖ ≤ 2
  · have h := hC δ hδ0 hδ1 w hw h2
    have hs0 : 0 ≤ ‖w‖ := norm_nonneg _
    have e : seedT δ w - seedT δ 0 =
        (airyTwistedLaplaceC (uctFstarDelta δ) w + (ceK : ℂ) * δ + uctC * w ^ (1 / 2 : ℂ) +
          (δ : ℂ) * (ceK : ℂ) * uctA1 * w) - uctC * w ^ (1 / 2 : ℂ) - (δ : ℂ) * (ceK : ℂ) * uctA1 * w := by
      rw [seedT_zero hδ0 hδ1]; unfold seedT; ring
    rw [e]
    have h3 := rpow_three_half_le hs0 h2
    have h4 := self_le_two_rpow_half hs0 h2
    have hp : 0 ≤ ‖w‖ ^ (1 / 2 : ℝ) := Real.rpow_nonneg hs0 _
    calc _ ≤ ‖airyTwistedLaplaceC (uctFstarDelta δ) w + (ceK : ℂ) * δ + uctC * w ^ (1 / 2 : ℂ) +
          (δ : ℂ) * (ceK : ℂ) * uctA1 * w‖ + ‖uctC * w ^ (1 / 2 : ℂ)‖ + ‖(δ : ℂ) * (ceK : ℂ) * uctA1 * w‖ := by
          exact (norm_sub_le _ _).trans (add_le_add_left (norm_sub_le _ _) _) |>.trans_eq (by ring)
      _ ≤ C * ‖w‖ ^ (3 / 2 : ℝ) + ‖uctC‖ * ‖w‖ ^ (1 / 2 : ℝ) + |δ| * ‖(ceK : ℂ)‖ * ‖uctA1‖ * ‖w‖ := by
          have e2 : ‖(δ : ℂ) * (ceK : ℂ) * uctA1 * w‖ = |δ| * ‖(ceK : ℂ)‖ * ‖uctA1‖ * ‖w‖ := by
            simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          rw [norm_mul uctC, CtOuter.norm_cpow_half, e2]
          gcongr
      _ ≤ C * (2 * ‖w‖ ^ (1 / 2 : ℝ)) + ‖uctC‖ * ‖w‖ ^ (1 / 2 : ℝ) +
            |δ| * ‖(ceK : ℂ)‖ * ‖uctA1‖ * (2 * ‖w‖ ^ (1 / 2 : ℝ)) := by gcongr
      _ = (2 * C + ‖uctC‖ + 2 * (|δ| * ‖(ceK : ℂ)‖ * ‖uctA1‖)) * ‖w‖ ^ (1 / 2 : ℝ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hp
  · have h2' : 2 < ‖w‖ := not_le.mp h2
    have h1 : 1 ≤ ‖w‖ ^ (1 / 2 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
    have : ‖seedT δ w - seedT δ 0‖ ≤ 2 * B := by
      refine (norm_sub_le _ _).trans ?_
      have a1 := hB w hw
      have a2 := hB 0 (by simp)
      linarith
    calc _ ≤ 2 * B := this
      _ ≤ 2 * B * ‖w‖ ^ (1 / 2 : ℝ) := by nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)


theorem seedW_oneSub {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (δ c : ℝ) {ζ : ℂ} (hζ : ζ ∈ closedStrip) :
    seedW ε δ c (1 - ζ) = ε * seedW ε δ c ζ := by
  unfold seedW
  rw [uctSeedZ_oneSub hε, outerHbar_oneSub hζ, sub_sub_cancel]
  ring

lemma seedW_bdd {ε δ c : ℝ} (hc : 0 < c) : ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ ζ : ℂ, 0 ≤ ζ.re → ζ.re ≤ 1 → ‖seedW ε δ c ζ‖ ≤ Cb := by
  obtain ⟨C, hC⟩ := (seedW_stripM1 (ε := ε) (δ := δ) hc).bound
  refine ⟨max C 0, le_max_right _ _, fun ζ h0 h1 => ?_⟩
  have := hC ζ h0 h1
  have hp : (1 + |ζ.im|) ^ (-(2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg ζ.im]) (by norm_num)
  have hp0 : 0 ≤ (1 + |ζ.im|) ^ (-(2 : ℝ)) := Real.rpow_nonneg (by linarith [abs_nonneg ζ.im]) _
  calc ‖seedW ε δ c ζ‖ ≤ C * (1 + |ζ.im|) ^ (-(2 : ℝ)) := this
    _ ≤ max C 0 * (1 + |ζ.im|) ^ (-(2 : ℝ)) := mul_le_mul_of_nonneg_right (le_max_left _ _) hp0
    _ ≤ max C 0 * 1 := mul_le_mul_of_nonneg_left hp (le_max_right _ _)
    _ = _ := mul_one _

lemma holo_lip_zero {f : ℂ → ℂ} {r ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ < r) (hf : DifferentiableOn ℂ f (ball (0 : ℂ) r)) :
    ∃ L M : ℝ, 0 ≤ L ∧ 0 ≤ M ∧ ∀ z : ℂ, ‖z‖ ≤ ρ → ‖f z - f 0‖ ≤ L * ‖z‖ ∧ ‖f z‖ ≤ M := by
  have hsub : closedBall (0 : ℂ) ρ ⊆ ball (0 : ℂ) r := closedBall_subset_ball hρ
  have hd : DifferentiableOn ℂ (deriv f) (ball (0 : ℂ) r) := hf.deriv isOpen_ball
  obtain ⟨L, hL⟩ := (isCompact_closedBall (0 : ℂ) ρ).exists_bound_of_continuousOn (hd.continuousOn.mono hsub)
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) ρ).exists_bound_of_continuousOn (hf.continuousOn.mono hsub)
  refine ⟨max L 0, max M 0, le_max_right _ _, le_max_right _ _, fun z hz => ?_⟩
  have hzm : z ∈ closedBall (0 : ℂ) ρ := by simpa using hz
  have h0m : (0 : ℂ) ∈ closedBall (0 : ℂ) ρ := by simp [hρ0]
  refine ⟨?_, (hM z hzm).trans (le_max_left _ _)⟩
  have := Convex.norm_image_sub_le_of_norm_deriv_le (f := f) (s := closedBall (0 : ℂ) ρ) (C := max L 0)
    (fun x hx => hf.differentiableAt (isOpen_ball.mem_nhds (hsub hx)))
    (fun x hx => (hL x hx).trans (le_max_left _ _)) (convex_closedBall _ _) h0m hzm
  simpa using this


/-- `Q = T(a)⁻¹ Z_ε e^{-H_0} T(a(1-ζ))`, the factor of `W^seed` holomorphic on `D(0,1/2)`. -/
noncomputable def seedQ (ε δ c : ℝ) (ζ : ℂ) : ℂ :=
  (seedT δ (seedScale c : ℂ))⁻¹ * (uctSeedZ ε ζ * Complex.exp (-H0 ζ) * seedT δ ((seedScale c : ℂ) * (1 - ζ)))

lemma seedQ_differentiableOn {ε δ c : ℝ} (hc : 0 < c) : DifferentiableOn ℂ (seedQ ε δ c) (ball (0 : ℂ) (1 / 2)) := by
  have ha := seedScale_pos hc
  have hZ : DifferentiableOn ℂ (uctSeedZ ε) (ball (0 : ℂ) (1 / 2)) :=
    (differentiableOn_uctSeedZ ε).mono fun ζ hζ => by
      have := Complex.abs_re_le_norm ζ
      have h2 : ‖ζ‖ < 1 / 2 := by simpa using hζ
      rw [abs_le] at this
      exact ⟨by linarith [this.1], by linarith [this.2]⟩
  have hT : DifferentiableOn ℂ (fun ζ : ℂ => seedT δ ((seedScale c : ℂ) * (1 - ζ))) (ball (0 : ℂ) (1 / 2)) :=
    (seedT_differentiableOn δ).comp (by fun_prop : Differentiable ℂ fun ζ : ℂ => (seedScale c : ℂ) * (1 - ζ)).differentiableOn
      fun ζ hζ => by
        show 0 < ((seedScale c : ℂ) * (1 - ζ)).re
        rw [re_mul_real_one_sub]
        have := Complex.re_le_norm ζ
        have h2 : ‖ζ‖ < 1 / 2 := by simpa using hζ
        exact mul_pos ha (by linarith)
  unfold seedQ
  exact ((hZ.mul differentiableOn_H0.neg.cexp).mul hT).const_mul _

lemma seedW_eq_Q_mul {ε δ c : ℝ} {ζ : ℂ} (hζ : ζ ∈ closedStrip) (hb : ζ ∈ ball (0 : ℂ) (1 / 2)) :
    seedW ε δ c ζ = seedQ ε δ c ζ * seedT δ ((seedScale c : ℂ) * ζ) := by
  unfold seedW seedQ
  rw [outerHbar_eq_H0 hζ hb]
  ring

lemma le_rpow_half_of_le_one {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) : s ≤ s ^ (1 / 2 : ℝ) := by
  rcases h0.eq_or_lt with rfl | hs
  · simp
  · have : s ^ (1 / 2 : ℝ) * s ^ (1 / 2 : ℝ) = s := by rw [← Real.rpow_add hs]; norm_num
    have h3 : s ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one h0 h1 (by norm_num)
    nlinarith [Real.rpow_nonneg h0 (1 / 2 : ℝ)]

/-- **(M2) at `ζ = 0`** for `W^seed`: `|W(ζ) - W(0)| ≤ C |ζ|^{1/2}` on `‖ζ‖ ≤ 1/2`, `0 ≤ Re ζ ≤ 1`. -/
theorem seedW_holder0 {ε δ c : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hc : 0 < c) :
    ∃ CH : ℝ, ∀ ζ : ℂ, 0 ≤ ζ.re → ζ.re ≤ 1 → ‖ζ‖ ≤ 1 / 2 → ‖seedW ε δ c ζ - seedW ε δ c 0‖ ≤ CH * ‖ζ‖ ^ (1 / 2 : ℝ) := by
  have ha := seedScale_pos hc
  obtain ⟨L, M, hL0, hM0, hLM⟩ := holo_lip_zero (f := seedQ ε δ c) (r := 1 / 2) (ρ := 1 / 3) (by norm_num) (by norm_num)
    (seedQ_differentiableOn hc)
  obtain ⟨CT, hCT0, hCT⟩ := seedT_holder hδ0 hδ1
  obtain ⟨Cb, hCb0, hCb⟩ := seedW_bdd (ε := ε) (δ := δ) hc
  have h00 : (0 : ℂ) ∈ closedStrip := ⟨by simp, by simp⟩
  have hball0 : (0 : ℂ) ∈ ball (0 : ℂ) (1 / 2) := by simp
  set T0 : ℝ := ‖seedT δ 0‖ with hT0
  refine ⟨max (M * CT * (seedScale c) ^ (1 / 2 : ℝ) + L * T0) (4 * Cb), fun ζ h0 h1 hζ => ?_⟩
  have hs0 : 0 ≤ ‖ζ‖ := norm_nonneg _
  have hp : 0 ≤ ‖ζ‖ ^ (1 / 2 : ℝ) := Real.rpow_nonneg hs0 _
  by_cases hnear : ‖ζ‖ ≤ 1 / 3
  · have hmem : ζ ∈ ball (0 : ℂ) (1 / 2) := by simp; linarith
    obtain ⟨hlip, hbd⟩ := hLM ζ hnear
    rw [seedW_eq_Q_mul ⟨h0, h1⟩ hmem, seedW_eq_Q_mul h00 hball0]
    have hTh := hCT ((seedScale c : ℂ) * ζ) (by rw [re_mul_real]; exact mul_nonneg ha.le h0)
    have hn : ‖(seedScale c : ℂ) * ζ‖ ^ (1 / 2 : ℝ) = (seedScale c) ^ (1 / 2 : ℝ) * ‖ζ‖ ^ (1 / 2 : ℝ) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha,
        Real.mul_rpow ha.le hs0]
    rw [hn] at hTh
    simp only [mul_zero] at hTh ⊢
    have e : seedQ ε δ c ζ * seedT δ ((seedScale c : ℂ) * ζ) - seedQ ε δ c 0 * seedT δ 0 =
        seedQ ε δ c ζ * (seedT δ ((seedScale c : ℂ) * ζ) - seedT δ 0) + (seedQ ε δ c ζ - seedQ ε δ c 0) * seedT δ 0 := by
      ring
    rw [e]
    have h4 := le_rpow_half_of_le_one hs0 (by linarith : ‖ζ‖ ≤ 1)
    calc _ ≤ ‖seedQ ε δ c ζ‖ * ‖seedT δ ((seedScale c : ℂ) * ζ) - seedT δ 0‖ +
          ‖seedQ ε δ c ζ - seedQ ε δ c 0‖ * ‖seedT δ 0‖ :=
          (norm_add_le _ _).trans (by rw [norm_mul, norm_mul])
      _ ≤ M * (CT * ((seedScale c) ^ (1 / 2 : ℝ) * ‖ζ‖ ^ (1 / 2 : ℝ))) + (L * ‖ζ‖) * T0 := by
          gcongr
      _ ≤ M * (CT * ((seedScale c) ^ (1 / 2 : ℝ) * ‖ζ‖ ^ (1 / 2 : ℝ))) + (L * ‖ζ‖ ^ (1 / 2 : ℝ)) * T0 := by
          gcongr
      _ = (M * CT * (seedScale c) ^ (1 / 2 : ℝ) + L * T0) * ‖ζ‖ ^ (1 / 2 : ℝ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hp
  · have hfar : 1 / 3 < ‖ζ‖ := not_le.mp hnear
    have hhalf : 1 ≤ 2 * ‖ζ‖ ^ (1 / 2 : ℝ) := by
      have : (1 / 2 : ℝ) ^ (2 : ℝ) < ‖ζ‖ := by norm_num; linarith
      have h5 : (1 / 2 : ℝ) < ‖ζ‖ ^ (1 / 2 : ℝ) := by
        have := Real.rpow_lt_rpow (by norm_num) this (by norm_num : (0 : ℝ) < 1 / 2)
        rwa [← Real.rpow_mul (by norm_num), show (2 : ℝ) * (1 / 2) = 1 by norm_num, Real.rpow_one] at this
      linarith
    have h5 : ‖seedW ε δ c ζ - seedW ε δ c 0‖ ≤ 2 * Cb :=
      (norm_sub_le _ _).trans (by
        have := hCb ζ h0 h1
        have := hCb 0 (by simp) (by simp)
        linarith)
    calc _ ≤ 2 * Cb := h5
      _ ≤ 2 * Cb * (2 * ‖ζ‖ ^ (1 / 2 : ℝ)) := by nlinarith
      _ = 4 * Cb * ‖ζ‖ ^ (1 / 2 : ℝ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hp

/-- **(M2) at `ζ = 1`** for `W^seed`, by `W(1-ζ) = ε W(ζ)`. -/
theorem seedW_holder1 {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {δ c : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hc : 0 < c) :
    ∃ CH : ℝ, ∀ ζ : ℂ, 0 ≤ ζ.re → ζ.re ≤ 1 → ‖1 - ζ‖ ≤ 1 / 2 → ‖seedW ε δ c ζ - seedW ε δ c 1‖ ≤ CH * ‖1 - ζ‖ ^ (1 / 2 : ℝ) := by
  obtain ⟨CH, hCH⟩ := seedW_holder0 (ε := ε) hδ0 hδ1 hc
  refine ⟨CH, fun ζ h0 h1 hζ => ?_⟩
  have hcl : (1 - ζ) ∈ closedStrip := ⟨by simp; exact h1, by simp; exact h0⟩
  have hcl' : ζ ∈ closedStrip := ⟨h0, h1⟩
  have e1 := seedW_oneSub hε δ c hcl
  have e2 := seedW_oneSub hε δ c (⟨by simp, by simp⟩ : (0 : ℂ) ∈ closedStrip)
  simp only [sub_sub_cancel, sub_zero] at e1 e2
  have hεn : ‖(ε : ℂ)‖ = 1 := by rcases hε with h | h <;> simp [h]
  have e3 : seedW ε δ c ζ - seedW ε δ c 1 = (ε : ℂ) * (seedW ε δ c (1 - ζ) - seedW ε δ c 0) := by
    rw [e1, e2]
    ring
  rw [e3, norm_mul, hεn, one_mul]
  exact hCH (1 - ζ) (by simp; exact h1) (by simp; exact h0 |>.trans' (le_refl _) |> fun _ => by simpa using h0) hζ

/-- info: 'FormalResearch.SignUncertainty.seedT_holder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms seedT_holder

/-- info: 'FormalResearch.SignUncertainty.seedW_oneSub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms seedW_oneSub

/-- info: 'FormalResearch.SignUncertainty.seedW_holder0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms seedW_holder0

/-- info: 'FormalResearch.SignUncertainty.seedW_holder1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms seedW_holder1

end FormalResearch.SignUncertainty
