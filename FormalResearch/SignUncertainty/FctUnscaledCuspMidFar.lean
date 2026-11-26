/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctUnscaledCuspMidPieces

/-!
# `fct:unscaled-cusp`, regime `c^{-2/3} ≤ u ≤ 1`: the far piece `[2t₀, ∞)` (F2a)

Source: `CFT/sign_uncertainty/paper/constant_terms_five.tex`, Lemma `fct:unscaled-cusp`, second estimate.

One integration by parts on `[2t₀, N]` with `P₁ = c κ₄ x²/(1+x²)` (`κ₄ = 3κ₁/8`, by `CuspPhase.far_lower`) and
`P₂ = c κ₃ x/(1+x²)`: the majorant integrand equals `Q e^{-ηx/2}(x^{-5/2} + x^{-1/2})`, `Q = K (1 + κ₃/κ₄)/(c κ₄)`, and
`N → ∞` is taken with `norm_Ioi_le`.

Class: proved.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped Real

namespace FormalResearch.SignUncertainty.FctUnscaledCusp

open FormalResearch.SignUncertainty FormalResearch.SignUncertainty.FctCuspEdge

/-! ### Elementary facts -/

/-- `Γ_η = ∫_0^∞ x^{-1/2} e^{-ηx/2} dx`. -/
noncomputable def cuspGam (η : ℝ) : ℝ := ∫ x in Ioi (0 : ℝ), x ^ (-(1 : ℝ) / 2) * Real.exp (-(η / 2) * x)

lemma cuspGam_integrableOn {η : ℝ} (hη : 0 < η) :
    IntegrableOn (fun x : ℝ => x ^ (-(1 : ℝ) / 2) * Real.exp (-(η / 2) * x)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := -(1 : ℝ) / 2) (b := η / 2) (by norm_num)
    one_pos (by positivity)
  refine h.congr_fun (fun x _ => ?_) measurableSet_Ioi
  simp

/-- `∫_α^N x^{-1/2} e^{-ηx/2} ≤ Γ_η`. -/
lemma integral_isqrt_exp_le {η α N : ℝ} (hη : 0 < η) (hα : 0 < α) (hαN : α ≤ N) :
    ∫ x in α..N, x ^ (-(1 : ℝ) / 2) * Real.exp (-(η / 2) * x) ≤ cuspGam η := by
  rw [intervalIntegral.integral_of_le hαN]
  unfold cuspGam
  refine setIntegral_mono_set (cuspGam_integrableOn hη) ?_ ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have : 0 < x := hx
    positivity
  · exact ae_of_all _ (fun x hx => Ioi_subset_Ioi hα.le (Ioc_subset_Ioi_self hx))

lemma cuspGam_nonneg (η : ℝ) : 0 ≤ cuspGam η :=
  setIntegral_nonneg measurableSet_Ioi fun x hx => by
    have : 0 < x := hx
    positivity

/-- `∫_α^N x^{-5/2} ≤ (2/3) α^{-3/2}`, with `α^{-3/2} = ((√α)³)⁻¹`. -/
lemma integral_rpow_neg_five_half_le {α N : ℝ} (hα : 0 < α) (hαN : α ≤ N) :
    ∫ x in α..N, x ^ (-(5 : ℝ) / 2) ≤ 2 / 3 * ((Real.sqrt α ^ 3)⁻¹) := by
  rw [integral_rpow (Or.inr ⟨by norm_num, by
    rw [uIcc_of_le hαN]; intro hm; exact absurd hm.1 (not_le.2 hα)⟩)]
  have key : ∀ y : ℝ, 0 < y → y ^ (-(5 : ℝ) / 2 + 1) = ((Real.sqrt y) ^ 3)⁻¹ := by
    intro y hy
    rw [show -(5 : ℝ) / 2 + 1 = -(3 / 2) by norm_num, Real.rpow_neg hy.le,
      show (3 : ℝ) / 2 = 1 / 2 * ((3 : ℕ) : ℝ) by norm_num, Real.rpow_mul hy.le, Real.rpow_natCast,
      ← Real.sqrt_eq_rpow]
  rw [key α hα, key N (hα.trans_le hαN)]
  have : 0 ≤ ((Real.sqrt N) ^ 3)⁻¹ := by positivity
  rw [show -(5 : ℝ) / 2 + 1 = -(3 / 2) by norm_num]
  have h2 : (((Real.sqrt N) ^ 3)⁻¹ - ((Real.sqrt α) ^ 3)⁻¹) / (-(3 / 2)) ≤ 2 / 3 * ((Real.sqrt α) ^ 3)⁻¹ := by
    rw [div_le_iff_of_neg (by norm_num)]
    nlinarith
  exact h2


lemma rpow_sq_half {y : ℝ} (hy : 0 < y) : (y ^ 2) ^ ((1 : ℝ) / 2) = y := by
  rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hy.le]

lemma rpow_sq_neg_half {y : ℝ} (hy : 0 < y) : (y ^ 2) ^ (-(1 : ℝ) / 2) = y⁻¹ := by
  rw [show -(1 : ℝ) / 2 = -((1 : ℝ) / 2) by ring, Real.rpow_neg (by positivity), rpow_sq_half hy]

lemma rpow_sq_neg_five_half {y : ℝ} (hy : 0 < y) : (y ^ 2) ^ (-(5 : ℝ) / 2) = (y ^ 5)⁻¹ := by
  rw [show -(5 : ℝ) / 2 = -((5 : ℝ) / 2) by ring, Real.rpow_neg (by positivity),
    ← Real.rpow_natCast y 2, ← Real.rpow_mul hy.le,
    show ((2 : ℕ) : ℝ) * (5 / 2) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

section Piece3

variable {𝔪 : ℝ → ℝ} {κ₁ κ₂ C₂ C₀ η Ca M : ℝ} {a : ℝ → ℂ}

/-- The majorant integrand of the far piece: `B₁/P₁ + B₀ P₂/P₁² = Q e^{-ηx/2}(x^{-5/2} + x^{-1/2})`. -/
lemma far_majorant_eq {K c k4 k3 η x : ℝ} (hc : 0 < c) (hk4 : 0 < k4) (hx : 0 < x) :
    K * (x ^ (-(1 : ℝ) / 2) * Real.exp (-(η / 2) * x)) / (c * (k4 * (x ^ 2 / (1 + x ^ 2)))) +
      K * (x ^ ((1 : ℝ) / 2) * Real.exp (-(η / 2) * x)) * (c * k3 * (x / (1 + x ^ 2))) /
        (c * (k4 * (x ^ 2 / (1 + x ^ 2)))) ^ 2 =
    K * (1 + k3 / k4) / (c * k4) * ((x ^ (-(5 : ℝ) / 2) + x ^ (-(1 : ℝ) / 2)) * Real.exp (-(η / 2) * x)) := by
  obtain ⟨y, hy, rfl⟩ : ∃ y, 0 < y ∧ x = y ^ 2 := ⟨Real.sqrt x, Real.sqrt_pos.2 hx, (Real.sq_sqrt hx.le).symm⟩
  rw [rpow_sq_half hy, rpow_sq_neg_half hy, rpow_sq_neg_five_half hy]
  generalize Real.exp (-(η / 2) * y ^ 2) = E
  field_simp

/-- The boundary term of the far piece: `B₀/P₁ = K/(c κ₄) e^{-ηx/2}((√x)⁻³ + √x)`. -/
lemma far_boundary_eq {K c k4 η x : ℝ} (hc : 0 < c) (hk4 : 0 < k4) (hx : 0 < x) :
    K * (x ^ ((1 : ℝ) / 2) * Real.exp (-(η / 2) * x)) / (c * (k4 * (x ^ 2 / (1 + x ^ 2)))) =
    K / (c * k4) * (((Real.sqrt x ^ 3)⁻¹ + Real.sqrt x) * Real.exp (-(η / 2) * x)) := by
  rw [← Real.sqrt_eq_rpow]
  obtain ⟨y, hy, rfl⟩ : ∃ y, 0 < y ∧ x = y ^ 2 := ⟨Real.sqrt x, Real.sqrt_pos.2 hx, (Real.sq_sqrt hx.le).symm⟩
  rw [Real.sqrt_sq hy.le]
  generalize Real.exp (-(η / 2) * y ^ 2) = E
  field_simp

/-- The constants of the far piece (`k₄ = 3κ₁/8`): `E₁ = (1 + (2/3)(1+κ₃/k₄))/k₄`, `E₂ = 2/k₄`,
`E₃ = (1+κ₃/k₄) Γ_η/k₄`. -/
noncomputable def cuspE1 (κ₁ κ₂ : ℝ) : ℝ := (1 + 2 / 3 * (1 + cuspK3 κ₂ / (3 * κ₁ / 8))) / (3 * κ₁ / 8)

noncomputable def cuspE2 (κ₁ : ℝ) : ℝ := 2 / (3 * κ₁ / 8)

noncomputable def cuspE3 (η κ₁ κ₂ : ℝ) : ℝ := (1 + cuspK3 κ₂ / (3 * κ₁ / 8)) * cuspGam η / (3 * κ₁ / 8)

/-- **Piece 3** of the second estimate: `‖∫_{2t₀}^∞ e^{icφ} a‖ ≤ K (E₁ r⁻³ + E₂ r + E₃)/c`, `r = √t₀`. -/
lemma cuspMid_piece3 (h : CuspPhase 𝔪 κ₁ κ₂ C₂ C₀) (ha : CuspAmpPos η Ca M a) (hη : 0 < η) (hCa : 0 ≤ Ca)
    (hM : 0 ≤ M) {c u r : ℝ} (hc : 0 < c) (hr : 0 < r) (hv : 𝔪 (r ^ 2) = u) :
    ‖∫ x in Ioi (2 * r ^ 2), Complex.exp (Complex.I * ((c * cuspPhase 𝔪 u x : ℝ) : ℂ)) * a x‖ ≤
      Ca * M * ampC η * (cuspE1 κ₁ κ₂ * (r ^ 3)⁻¹ + cuspE2 κ₁ * r + cuspE3 η κ₁ κ₂) / c := by
  have hκ := h.κ₁_pos
  have hκ3 := h.κ₃_pos
  have ht₀ : 0 < r ^ 2 := by positivity
  set K : ℝ := Ca * M * ampC η with hK
  have hK0 : 0 ≤ K := cuspK_nonneg hη hCa hM
  set k4 : ℝ := 3 * κ₁ / 8 with hk4
  have hk4pos : 0 < k4 := by positivity
  set Q : ℝ := K * (1 + cuspK3 κ₂ / k4) / (c * k4) with hQ
  have hQ0 : 0 ≤ Q := by positivity
  set α : ℝ := 2 * r ^ 2 with hα
  have hαpos : 0 < α := by positivity
  have hF : IntegrableOn (fun x => Complex.exp (Complex.I * ((c * cuspPhase 𝔪 u x : ℝ) : ℂ)) * a x) (Ioi α) :=
    (cuspF_integrableOn h.continuous ha hη hCa hM c u).mono_set (Ioi_subset_Ioi hαpos.le)
  have hEle : ∀ x : ℝ, 0 ≤ x → Real.exp (-(η / 2) * x) ≤ 1 := fun x hx =>
    Real.exp_le_one_iff.2 (by nlinarith)
  have hEcont : Continuous fun x : ℝ => Real.exp (-(η / 2) * x) := by fun_prop
  have hsa1 : r ≤ Real.sqrt α := by
    apply Real.le_sqrt_of_sq_le; rw [hα]; nlinarith [sq_nonneg r]
  have hsa2 : Real.sqrt α ≤ 2 * r := by
    rw [Real.sqrt_le_left (by positivity), hα]; nlinarith [sq_nonneg r]
  -- the remainder tends to zero
  have hRlim : Tendsto (fun N : ℝ => K / (c * k4) * (((Real.sqrt N ^ 3)⁻¹ + Real.sqrt N) * Real.exp (-(η / 2) * N)))
      atTop (𝓝 0) := by
    have t1 : Tendsto (fun N : ℝ => (Real.sqrt N ^ 3)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop (by norm_num)).comp Real.tendsto_sqrt_atTop)
    have t2 : Tendsto (fun N : ℝ => Real.exp (-(η / 2) * N)) atTop (𝓝 0) := by
      have := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 (η / 2) (by positivity)
      simpa using this
    have t3 : Tendsto (fun N : ℝ => Real.sqrt N * Real.exp (-(η / 2) * N)) atTop (𝓝 0) := by
      have := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((1 : ℝ) / 2) (η / 2) (by positivity)
      refine this.congr (fun N => ?_)
      rw [Real.sqrt_eq_rpow]
    have t4 := (t1.mul t2).add t3
    rw [zero_mul, add_zero] at t4
    have t5 := t4.const_mul (K / (c * k4))
    rw [mul_zero] at t5
    refine t5.congr (fun N => ?_)
    ring
  refine norm_Ioi_le (A := K / (c * k4) * ((r ^ 3)⁻¹ + 2 * r) + Q * (2 / 3 * (r ^ 3)⁻¹ + cuspGam η)) hF hRlim ?_ |>.trans
    (le_of_eq ?_)
  swap
  · simp only [cuspE1, cuspE2, cuspE3, hQ, ← hk4]
    field_simp
    ring
  intro N hN
  have hNpos : 0 < N := hαpos.trans_le hN
  have hnot0 : (0 : ℝ) ∉ uIcc α N := by
    rw [uIcc_of_le hN]; intro hm; exact absurd hm.1 (not_le.2 hαpos)
  have Ii1 : IntervalIntegrable (fun x : ℝ => x ^ (-(5 : ℝ) / 2)) volume α N :=
    intervalIntegral.intervalIntegrable_rpow (Or.inr hnot0)
  have Ii2 : IntervalIntegrable (fun x : ℝ => x ^ (-(1 : ℝ) / 2)) volume α N :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have Ii3 : IntervalIntegrable (fun x : ℝ => x ^ (-(1 : ℝ) / 2) * Real.exp (-(η / 2) * x)) volume α N :=
    Ii2.mul_continuousOn hEcont.continuousOn
  have hGf : ∀ x ∈ uIcc α N, K * (x ^ (-(1 : ℝ) / 2) * Real.exp (-(η / 2) * x)) / (c * (k4 * (x ^ 2 / (1 + x ^ 2)))) +
      K * (x ^ ((1 : ℝ) / 2) * Real.exp (-(η / 2) * x)) * (c * cuspK3 κ₂ * (x / (1 + x ^ 2))) /
        (c * (k4 * (x ^ 2 / (1 + x ^ 2)))) ^ 2 =
      Q * ((x ^ (-(5 : ℝ) / 2) + x ^ (-(1 : ℝ) / 2)) * Real.exp (-(η / 2) * x)) := by
    intro x hx
    rw [uIcc_of_le hN] at hx
    exact far_majorant_eq hc hk4pos (hαpos.trans_le hx.1)
  have hint : IntervalIntegrable (fun x : ℝ =>
      K * (x ^ (-(1 : ℝ) / 2) * Real.exp (-(η / 2) * x)) / (c * (k4 * (x ^ 2 / (1 + x ^ 2)))) +
      K * (x ^ ((1 : ℝ) / 2) * Real.exp (-(η / 2) * x)) * (c * cuspK3 κ₂ * (x / (1 + x ^ 2))) /
        (c * (k4 * (x ^ 2 / (1 + x ^ 2)))) ^ 2) volume α N := by
    have := ((Ii1.add Ii2).mul_continuousOn hEcont.continuousOn).const_mul Q
    refine this.congr ?_
    intro x hx
    rw [uIoc_of_le hN] at hx
    exact (hGf x (by rw [uIcc_of_le hN]; exact ⟨hx.1.le, hx.2⟩)).symm
  have hib := cusp_ibp_one h ha hc hαpos hN (u := u)
    (B0 := fun x => K * (x ^ ((1 : ℝ) / 2) * Real.exp (-(η / 2) * x)))
    (B1 := fun x => K * (x ^ (-(1 : ℝ) / 2) * Real.exp (-(η / 2) * x)))
    (P1 := fun x => c * (k4 * (x ^ 2 / (1 + x ^ 2))))
    (P2 := fun x => c * cuspK3 κ₂ * (x / (1 + x ^ 2)))
    (fun x hx => by
      have hx0 : 0 < x := hαpos.trans_le hx.1
      refine (ha.amp0 hη hCa hM hx0).trans (le_of_eq ?_)
      rfl)
    (fun x hx => by
      have hx0 : 0 < x := hαpos.trans_le hx.1
      exact ha.amp1 hη hCa hM hx0)
    (fun x hx => by
      have hx0 : 0 < x := hαpos.trans_le hx.1
      refine ⟨by positivity, ?_⟩
      have hfl := h.far_lower ht₀.le (by simpa [hα] using hx.1)
      rw [hv, ← hk4] at hfl
      have hpos : 0 < 𝔪 x - u := by
        have : 0 < k4 * (x ^ 2 / (1 + x ^ 2)) := by positivity
        linarith
      rw [abs_sub_comm, abs_of_pos hpos]
      exact mul_le_mul_of_nonneg_left hfl hc.le)
    (fun x hx => by
      have hx0 : 0 < x := hαpos.trans_le hx.1
      have := h.deriv_le_w hx0
      unfold cuspW at this
      calc c * deriv 𝔪 x ≤ c * (cuspK3 κ₂ * (x / (1 + x ^ 2))) := mul_le_mul_of_nonneg_left this hc.le
        _ = c * cuspK3 κ₂ * (x / (1 + x ^ 2)) := by ring)
    hint
  refine hib.trans ?_
  -- boundary term at `N` is the remainder
  rw [far_boundary_eq hc hk4pos hNpos]
  -- boundary term at `α`
  have hbα : K * (α ^ ((1 : ℝ) / 2) * Real.exp (-(η / 2) * α)) / (c * (k4 * (α ^ 2 / (1 + α ^ 2)))) ≤
      K / (c * k4) * ((r ^ 3)⁻¹ + 2 * r) := by
    rw [far_boundary_eq hc hk4pos hαpos]
    have h1 : (Real.sqrt α ^ 3)⁻¹ ≤ (r ^ 3)⁻¹ :=
      inv_anti₀ (by positivity) (pow_le_pow_left₀ hr.le hsa1 3)
    have h2 : ((Real.sqrt α ^ 3)⁻¹ + Real.sqrt α) * Real.exp (-(η / 2) * α) ≤ (r ^ 3)⁻¹ + 2 * r := by
      have hE := hEle α hαpos.le
      have hE0 := (Real.exp_pos (-(η / 2) * α)).le
      have h3 : 0 ≤ (Real.sqrt α ^ 3)⁻¹ + Real.sqrt α := by positivity
      calc _ ≤ ((Real.sqrt α ^ 3)⁻¹ + Real.sqrt α) * 1 := mul_le_mul_of_nonneg_left hE h3
        _ ≤ _ := by linarith
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  -- the integral
  have hint2 : ∫ x in α..N, (K * (x ^ (-(1 : ℝ) / 2) * Real.exp (-(η / 2) * x)) / (c * (k4 * (x ^ 2 / (1 + x ^ 2)))) +
      K * (x ^ ((1 : ℝ) / 2) * Real.exp (-(η / 2) * x)) * (c * cuspK3 κ₂ * (x / (1 + x ^ 2))) /
        (c * (k4 * (x ^ 2 / (1 + x ^ 2)))) ^ 2) ≤ Q * (2 / 3 * (r ^ 3)⁻¹ + cuspGam η) := by
    have hmaj : IntervalIntegrable (fun x : ℝ => Q * (x ^ (-(5 : ℝ) / 2) + x ^ (-(1 : ℝ) / 2) * Real.exp (-(η / 2) * x)))
        volume α N := (Ii1.add Ii3).const_mul Q
    have hle : ∫ x in α..N, (K * (x ^ (-(1 : ℝ) / 2) * Real.exp (-(η / 2) * x)) / (c * (k4 * (x ^ 2 / (1 + x ^ 2)))) +
        K * (x ^ ((1 : ℝ) / 2) * Real.exp (-(η / 2) * x)) * (c * cuspK3 κ₂ * (x / (1 + x ^ 2))) /
          (c * (k4 * (x ^ 2 / (1 + x ^ 2)))) ^ 2) ≤
        ∫ x in α..N, Q * (x ^ (-(5 : ℝ) / 2) + x ^ (-(1 : ℝ) / 2) * Real.exp (-(η / 2) * x)) := by
      refine intervalIntegral.integral_mono_on hN hint hmaj (fun x hx => ?_)
      rw [hGf x (by rw [uIcc_of_le hN]; exact hx)]
      have hx0 : 0 < x := hαpos.trans_le hx.1
      have hE := hEle x hx0.le
      have hg1 : 0 ≤ x ^ (-(5 : ℝ) / 2) := Real.rpow_nonneg hx0.le _
      have hg2 : 0 ≤ x ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg hx0.le _
      have hE0 := (Real.exp_pos (-(η / 2) * x)).le
      refine mul_le_mul_of_nonneg_left ?_ hQ0
      nlinarith [mul_nonneg hg1 (sub_nonneg.2 hE)]
    refine hle.trans ?_
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add Ii1 Ii3]
    refine mul_le_mul_of_nonneg_left ?_ hQ0
    have h1 := integral_rpow_neg_five_half_le hαpos hN
    have h2 := integral_isqrt_exp_le hη hαpos hN
    have h3 : (Real.sqrt α ^ 3)⁻¹ ≤ (r ^ 3)⁻¹ :=
      inv_anti₀ (by positivity) (pow_le_pow_left₀ hr.le hsa1 3)
    linarith
  linarith

end Piece3
