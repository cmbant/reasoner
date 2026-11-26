/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctUnscaledCuspFarLow

/-!
# `fct:unscaled-cusp`, regime `u ≥ 1`: the saddle piece `[t₀/2, 2t₀]` and the far piece `[2t₀, ∞)` (F2a)

Source: `CFT/sign_uncertainty/paper/constant_terms_five.tex`, Lemma `fct:unscaled-cusp`, third estimate.

* `cuspFar_saddle`: van der Corput on `[t₀/2, 2t₀]`, where `𝔪' ≥ κ₁/((κ₃+2) t₀)` (`CuspPhase.far_mid_deriv`) and the amplitude
  supremum and variation are `K t₀^{±1/2} e^{-ηt₀/4}`: `‖∫‖ ≤ K D₃ e^{-ηt₀/8}/√c`.
* `cuspFar_tail_raw`, `cuspFar_tail`: one integration by parts on `[2t₀, N]` (as in the second estimate, `cuspMid_piece3`, but
  keeping the exponential decay of the amplitude), `‖∫_{2t₀}^∞‖ ≤ (K/c) D₄ e^{-ηt₀/8}`.

Class: proved.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped Real

namespace FormalResearch.SignUncertainty.FctUnscaledCusp

open FormalResearch.SignUncertainty FormalResearch.SignUncertainty.FctCuspEdge

section Saddle

variable {𝔪 : ℝ → ℝ} {κ₁ κ₂ C₂ C₀ η Ca M : ℝ} {a : ℝ → ℂ}

/-- The constant of the saddle piece: `D₃ = 40 (1 + 8/η)/√q`, `q = κ₁/(κ₃+2)`. -/
noncomputable def cuspFarD3 (η κ₁ κ₂ : ℝ) : ℝ := 40 * (1 + 8 / η) / Real.sqrt (κ₁ / (cuspK3 κ₂ + 2))

/-- **The saddle piece** `[t₀/2, 2t₀]` for `u ≥ 1`. -/
lemma cuspFar_saddle (h : CuspPhase 𝔪 κ₁ κ₂ C₂ C₀) (ha : CuspAmpPos η Ca M a) (hη : 0 < η) (hCa : 0 ≤ Ca)
    (hM : 0 ≤ M) {c u t₀ : ℝ} (hc : 0 < c) (hu : 1 ≤ u) (ht₀ : 0 < t₀) (hv : 𝔪 t₀ = u) :
    ‖∫ x in (t₀ / 2)..(2 * t₀), Complex.exp (Complex.I * ((c * cuspPhase 𝔪 u x : ℝ) : ℂ)) * a x‖ ≤
      Ca * M * ampC η * cuspFarD3 η κ₁ κ₂ * Real.exp (-(η / 8) * t₀) / Real.sqrt c := by
  have hκ := h.κ₁_pos
  have hκ3 := h.κ₃_pos
  obtain ⟨r, hr, rfl⟩ : ∃ r, 0 < r ∧ t₀ = r ^ 2 := ⟨Real.sqrt t₀, Real.sqrt_pos.2 ht₀, (Real.sq_sqrt ht₀.le).symm⟩
  set K : ℝ := Ca * M * ampC η with hK
  have hK0 : 0 ≤ K := cuspK_nonneg hη hCa hM
  set q : ℝ := κ₁ / (cuspK3 κ₂ + 2) with hq
  have hqpos : 0 < q := by positivity
  set lam : ℝ := q * (r ^ 2)⁻¹ with hlam
  have hlampos : 0 < lam := by positivity
  set e₀ : ℝ := Real.exp (-(η / 4) * r ^ 2) with he₀
  have he0 : 0 < e₀ := Real.exp_pos _
  have hα : 0 < r ^ 2 / 2 := by positivity
  have hαβ : r ^ 2 / 2 ≤ 2 * r ^ 2 := by nlinarith [sq_nonneg r]
  have hsqx : ∀ x, r ^ 2 / 2 ≤ x → x ≤ 2 * r ^ 2 → Real.sqrt x ≤ 2 * r ∧ r / 2 ≤ Real.sqrt x := by
    intro x h1 h2
    constructor
    · rw [Real.sqrt_le_left (by positivity)]; nlinarith [sq_nonneg r]
    · apply Real.le_sqrt_of_sq_le; nlinarith [sq_nonneg r]
  have hEx : ∀ x, r ^ 2 / 2 ≤ x → Real.exp (-(η / 2) * x) ≤ e₀ := by
    intro x hx
    rw [he₀]; exact Real.exp_le_exp.2 (by nlinarith)
  have hM1 : ∀ x ∈ Icc (r ^ 2 / 2) (2 * r ^ 2), ‖a x‖ ≤ K * (2 * r * e₀) := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hα hx.1
    have h0 := ha.amp0 hη hCa hM hx0
    have hs := (hsqx x hx.1 hx.2).1
    rw [← Real.sqrt_eq_rpow] at h0
    have h1 : Real.sqrt x * Real.exp (-(η / 2) * x) ≤ 2 * r * e₀ :=
      mul_le_mul hs (hEx x hx.1) (Real.exp_pos _).le (by positivity)
    exact h0.trans (mul_le_mul_of_nonneg_left h1 hK0)
  have hM2 : ∀ x ∈ Icc (r ^ 2 / 2) (2 * r ^ 2), ‖deriv a x‖ ≤ K * (2 / r * e₀) := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hα hx.1
    have h0 := ha.amp1 hη hCa hM hx0
    have hs := (hsqx x hx.1 hx.2).2
    have e : x ^ (-(1 : ℝ) / 2) = (Real.sqrt x)⁻¹ := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hx0.le]; norm_num
    rw [e] at h0
    have h2 : (Real.sqrt x)⁻¹ ≤ 2 / r := by
      rw [inv_le_comm₀ (Real.sqrt_pos.2 hx0) (by positivity)]
      rw [inv_div]; exact hs
    have h1 : (Real.sqrt x)⁻¹ * Real.exp (-(η / 2) * x) ≤ 2 / r * e₀ :=
      mul_le_mul h2 (hEx x hx.1) (Real.exp_pos _).le (by positivity)
    exact h0.trans (mul_le_mul_of_nonneg_left h1 hK0)
  have hv2 := cusp_vdc h ha (η := η) (Ca := Ca) (M := M) (c := c) (u := u) hc hα hαβ hlampos
    (fun x hx => by
      have := h.far_mid_deriv (by positivity) hv hu hx.1 hx.2
      calc lam = κ₁ / ((cuspK3 κ₂ + 2) * r ^ 2) := by rw [hlam, hq]; field_simp
        _ ≤ _ := this) hM1 hM2 (by positivity)
  refine hv2.trans ?_
  have hsq : Real.sqrt (c * lam) = Real.sqrt c * (Real.sqrt q / r) := by
    rw [hlam, show c * (q * (r ^ 2)⁻¹) = c * (q / r ^ 2) by ring, Real.sqrt_mul hc.le,
      Real.sqrt_div hqpos.le, Real.sqrt_sq hr.le]
  rw [hsq]
  unfold cuspFarD3
  rw [← hq]
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  have hsq0 : 0 < Real.sqrt q := Real.sqrt_pos.2 hqpos
  have e1 : 8 * (K * (2 * r * e₀) + K * (2 / r * e₀) * (2 * r ^ 2 - r ^ 2 / 2)) /
      (Real.sqrt c * (Real.sqrt q / r)) = 40 * K * (e₀ * r ^ 2) / (Real.sqrt c * Real.sqrt q) := by
    field_simp; ring
  rw [e1]
  have hx := one_add_mul_exp_le (z := η / 8) (x := r ^ 2) (by positivity) (by positivity)
  have hee : e₀ = Real.exp (-(η / 8) * r ^ 2) * Real.exp (-(η / 8) * r ^ 2) := by
    rw [he₀, ← Real.exp_add]; congr 1; ring
  have e2 : 1 + 1 / (η / 8) = 1 + 8 / η := by field_simp
  rw [e2] at hx
  have hE8 : 0 < Real.exp (-(η / 8) * r ^ 2) := Real.exp_pos _
  have hb : e₀ * r ^ 2 ≤ (1 + 8 / η) * Real.exp (-(η / 8) * r ^ 2) := by
    have h1 : r ^ 2 * Real.exp (-(η / 8) * r ^ 2) ≤ 1 + 8 / η := by nlinarith [hE8]
    calc e₀ * r ^ 2 = (r ^ 2 * Real.exp (-(η / 8) * r ^ 2)) * Real.exp (-(η / 8) * r ^ 2) := by rw [hee]; ring
      _ ≤ (1 + 8 / η) * Real.exp (-(η / 8) * r ^ 2) := mul_le_mul_of_nonneg_right h1 hE8.le
  have hden : 0 < Real.sqrt c * Real.sqrt q := by positivity
  have e3 : K * (40 * (1 + 8 / η) / Real.sqrt q) * Real.exp (-(η / 8) * r ^ 2) / Real.sqrt c =
      40 * K * ((1 + 8 / η) * Real.exp (-(η / 8) * r ^ 2)) / (Real.sqrt c * Real.sqrt q) := by
    field_simp
  rw [e3]
  refine div_le_div_of_nonneg_right ?_ hden.le
  have : 0 ≤ 40 * K := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hb this]

end Saddle

section Tail

variable {𝔪 : ℝ → ℝ} {κ₁ κ₂ C₂ C₀ η Ca M : ℝ} {a : ℝ → ℂ}

/-- **The far piece, before simplification**: `α = 2 t₀`,
`‖∫_α^∞‖ ≤ K/(c k₄) ((√α³)⁻¹ + √α) e^{-ηα/2} + Q e^{-ηα/4} ((2/3)(√α³)⁻¹ + Γ_{η/2})`. -/
lemma cuspFar_tail_raw (h : CuspPhase 𝔪 κ₁ κ₂ C₂ C₀) (ha : CuspAmpPos η Ca M a) (hη : 0 < η) (hCa : 0 ≤ Ca)
    (hM : 0 ≤ M) {c u t₀ : ℝ} (hc : 0 < c) (ht₀ : 0 < t₀) (hv : 𝔪 t₀ = u) :
    ‖∫ x in Ioi (2 * t₀), Complex.exp (Complex.I * ((c * cuspPhase 𝔪 u x : ℝ) : ℂ)) * a x‖ ≤
      Ca * M * ampC η / (c * (3 * κ₁ / 8)) *
          (((Real.sqrt (2 * t₀) ^ 3)⁻¹ + Real.sqrt (2 * t₀)) * Real.exp (-(η / 2) * (2 * t₀))) +
      Ca * M * ampC η * (1 + cuspK3 κ₂ / (3 * κ₁ / 8)) / (c * (3 * κ₁ / 8)) *
          (Real.exp (-(η / 4) * (2 * t₀)) * (2 / 3 * (Real.sqrt (2 * t₀) ^ 3)⁻¹ + cuspGam (η / 2))) := by
  have hκ := h.κ₁_pos
  have hκ3 := h.κ₃_pos
  set K : ℝ := Ca * M * ampC η with hK
  have hK0 : 0 ≤ K := cuspK_nonneg hη hCa hM
  set k4 : ℝ := 3 * κ₁ / 8 with hk4
  have hk4pos : 0 < k4 := by positivity
  set Q : ℝ := K * (1 + cuspK3 κ₂ / k4) / (c * k4) with hQ
  have hQ0 : 0 ≤ Q := by positivity
  set α : ℝ := 2 * t₀ with hα
  have hαpos : 0 < α := by positivity
  have hF : IntegrableOn (fun x => Complex.exp (Complex.I * ((c * cuspPhase 𝔪 u x : ℝ) : ℂ)) * a x) (Ioi α) :=
    (cuspF_integrableOn h.continuous ha hη hCa hM c u).mono_set (Ioi_subset_Ioi hαpos.le)
  have hEc : Continuous fun x : ℝ => Real.exp (-(η / 2) * x) := by fun_prop
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
  have hεα : (0 : ℝ) ≤ Real.exp (-(η / 4) * α) := (Real.exp_pos _).le
  refine (norm_Ioi_le (A := K / (c * k4) * (((Real.sqrt α ^ 3)⁻¹ + Real.sqrt α) * Real.exp (-(η / 2) * α)) +
    Q * (Real.exp (-(η / 4) * α) * (2 / 3 * (Real.sqrt α ^ 3)⁻¹ + cuspGam (η / 2)))) hF hRlim ?_).trans
    (le_of_eq ?_)
  swap
  · rfl
  intro N hN
  have hNpos : 0 < N := hαpos.trans_le hN
  have hnot0 : (0 : ℝ) ∉ uIcc α N := by
    rw [uIcc_of_le hN]; intro hm; exact absurd hm.1 (not_le.2 hαpos)
  have Ii1 : IntervalIntegrable (fun x : ℝ => x ^ (-(5 : ℝ) / 2)) volume α N :=
    intervalIntegral.intervalIntegrable_rpow (Or.inr hnot0)
  have Ii2 : IntervalIntegrable (fun x : ℝ => x ^ (-(1 : ℝ) / 2)) volume α N :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hE'c : Continuous fun x : ℝ => Real.exp (-((η / 2) / 2) * x) := by fun_prop
  have Ii3 : IntervalIntegrable (fun x : ℝ => x ^ (-(1 : ℝ) / 2) * Real.exp (-((η / 2) / 2) * x)) volume α N :=
    Ii2.mul_continuousOn hE'c.continuousOn
  have Ii4 : IntervalIntegrable (fun x : ℝ => x ^ (-(5 : ℝ) / 2) * Real.exp (-(η / 2) * x)) volume α N :=
    Ii1.mul_continuousOn hEc.continuousOn
  have Ii5 : IntervalIntegrable (fun x : ℝ => x ^ (-(1 : ℝ) / 2) * Real.exp (-(η / 2) * x)) volume α N :=
    Ii2.mul_continuousOn hEc.continuousOn
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
    have := ((Ii4.add Ii5).const_mul Q)
    refine this.congr ?_
    intro x hx
    rw [uIoc_of_le hN] at hx
    have := hGf x (by rw [uIcc_of_le hN]; exact ⟨hx.1.le, hx.2⟩)
    simp only
    rw [this]; ring
  have hib := cusp_ibp_one h ha hc hαpos hN (u := u)
    (B0 := fun x => K * (x ^ ((1 : ℝ) / 2) * Real.exp (-(η / 2) * x)))
    (B1 := fun x => K * (x ^ (-(1 : ℝ) / 2) * Real.exp (-(η / 2) * x)))
    (P1 := fun x => c * (k4 * (x ^ 2 / (1 + x ^ 2))))
    (P2 := fun x => c * cuspK3 κ₂ * (x / (1 + x ^ 2)))
    (fun x hx => by
      have hx0 : 0 < x := hαpos.trans_le hx.1
      exact ha.amp0 hη hCa hM hx0)
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
  rw [far_boundary_eq hc hk4pos hNpos, far_boundary_eq hc hk4pos hαpos]
  -- the integral
  have hint2 : ∫ x in α..N, (K * (x ^ (-(1 : ℝ) / 2) * Real.exp (-(η / 2) * x)) / (c * (k4 * (x ^ 2 / (1 + x ^ 2)))) +
      K * (x ^ ((1 : ℝ) / 2) * Real.exp (-(η / 2) * x)) * (c * cuspK3 κ₂ * (x / (1 + x ^ 2))) /
        (c * (k4 * (x ^ 2 / (1 + x ^ 2)))) ^ 2) ≤
      Q * (Real.exp (-(η / 4) * α) * (2 / 3 * (Real.sqrt α ^ 3)⁻¹ + cuspGam (η / 2))) := by
    have hmaj : IntervalIntegrable (fun x : ℝ => Q * (Real.exp (-(η / 4) * α) *
        (x ^ (-(5 : ℝ) / 2) + x ^ (-(1 : ℝ) / 2) * Real.exp (-((η / 2) / 2) * x)))) volume α N :=
      ((Ii1.add Ii3).const_mul _).const_mul _
    have hle : ∫ x in α..N, (K * (x ^ (-(1 : ℝ) / 2) * Real.exp (-(η / 2) * x)) / (c * (k4 * (x ^ 2 / (1 + x ^ 2)))) +
        K * (x ^ ((1 : ℝ) / 2) * Real.exp (-(η / 2) * x)) * (c * cuspK3 κ₂ * (x / (1 + x ^ 2))) /
          (c * (k4 * (x ^ 2 / (1 + x ^ 2)))) ^ 2) ≤
        ∫ x in α..N, Q * (Real.exp (-(η / 4) * α) *
          (x ^ (-(5 : ℝ) / 2) + x ^ (-(1 : ℝ) / 2) * Real.exp (-((η / 2) / 2) * x))) := by
      refine intervalIntegral.integral_mono_on hN hint hmaj (fun x hx => ?_)
      rw [hGf x (by rw [uIcc_of_le hN]; exact hx)]
      have hx0 : 0 < x := hαpos.trans_le hx.1
      have hg1 : 0 ≤ x ^ (-(5 : ℝ) / 2) := Real.rpow_nonneg hx0.le _
      have hg2 : 0 ≤ x ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg hx0.le _
      have hE' : Real.exp (-((η / 2) / 2) * x) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
      have hEε' : Real.exp (-(η / 2) * x) ≤ Real.exp (-(η / 4) * α) * Real.exp (-((η / 2) / 2) * x) := by
        rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by nlinarith [hx.1])
      have hEε : Real.exp (-(η / 2) * x) ≤ Real.exp (-(η / 4) * α) := by
        refine hEε'.trans ?_
        calc _ ≤ Real.exp (-(η / 4) * α) * 1 := mul_le_mul_of_nonneg_left hE' hεα
          _ = _ := mul_one _
      refine mul_le_mul_of_nonneg_left ?_ hQ0
      have p1 := mul_le_mul_of_nonneg_left hEε hg1
      have p2 := mul_le_mul_of_nonneg_left hEε' hg2
      nlinarith [p1, p2]
    refine hle.trans ?_
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add Ii1 Ii3]
    refine mul_le_mul_of_nonneg_left ?_ hQ0
    refine mul_le_mul_of_nonneg_left ?_ hεα
    have h1 := integral_rpow_neg_five_half_le hαpos hN
    have h2 := integral_isqrt_exp_le (η := η / 2) (by positivity) hαpos hN
    linarith
  linarith

/-- The constant of the far piece. -/
noncomputable def cuspFarD4 (η κ₁ κ₂ : ℝ) : ℝ :=
  (1 / (3 * κ₁ / 8)) * (1 + cuspK3 κ₂ / 8) * (1 + 4 / η) +
    ((1 + cuspK3 κ₂ / (3 * κ₁ / 8)) / (3 * κ₁ / 8)) * (cuspK3 κ₂ / 12 * (1 + 8 / η) + cuspGam (η / 2))

/-- **The far piece** `[2t₀, ∞)` for `u ≥ 1`: `‖∫‖ ≤ (K/c) D₄ e^{-ηt₀/8}`. -/
lemma cuspFar_tail (h : CuspPhase 𝔪 κ₁ κ₂ C₂ C₀) (ha : CuspAmpPos η Ca M a) (hη : 0 < η) (hCa : 0 ≤ Ca)
    (hM : 0 ≤ M) {c u t₀ : ℝ} (hc : 0 < c) (hu : 1 ≤ u) (ht₀ : 0 < t₀) (hv : 𝔪 t₀ = u) :
    ‖∫ x in Ioi (2 * t₀), Complex.exp (Complex.I * ((c * cuspPhase 𝔪 u x : ℝ) : ℂ)) * a x‖ ≤
      Ca * M * ampC η / c * (cuspFarD4 η κ₁ κ₂ * Real.exp (-(η / 8) * t₀)) := by
  have hκ := h.κ₁_pos
  have hκ3 := h.κ₃_pos
  have hraw := cuspFar_tail_raw h ha hη hCa hM hc ht₀ hv
  refine hraw.trans ?_
  set K : ℝ := Ca * M * ampC η with hK
  have hK0 : 0 ≤ K := cuspK_nonneg hη hCa hM
  set k4 : ℝ := 3 * κ₁ / 8 with hk4
  have hk4pos : 0 < k4 := by positivity
  set κ₃ : ℝ := cuspK3 κ₂ with hκ₃
  set α : ℝ := 2 * t₀ with hα
  have hαpos : 0 < α := by positivity
  have hΓ : 0 ≤ cuspGam (η / 2) := cuspGam_nonneg _
  have h2s := h.two_le_sq ht₀ hv hu
  have hs0 : 0 < Real.sqrt α := Real.sqrt_pos.2 hαpos
  have hs2 : Real.sqrt α ^ 2 = α := Real.sq_sqrt hαpos.le
  have hs3 : (Real.sqrt α ^ 3)⁻¹ ≤ κ₃ / 8 * Real.sqrt α := by
    have h4 : α ^ 2 = Real.sqrt α ^ 4 := by
      calc α ^ 2 = (Real.sqrt α ^ 2) ^ 2 := by rw [hs2]
        _ = Real.sqrt α ^ 4 := by ring
    have e : (Real.sqrt α ^ 3)⁻¹ = Real.sqrt α / α ^ 2 := by
      rw [h4]; field_simp
    rw [e, div_le_iff₀ (by positivity)]
    have : 8 ≤ κ₃ * α ^ 2 := by rw [hα]; nlinarith
    nlinarith [mul_le_mul_of_nonneg_left this hs0.le]
  have hs1 : Real.sqrt α ≤ 1 + α := by
    rw [Real.sqrt_eq_rpow]; exact rpow_half_le_one_add hαpos
  have hA : (Real.sqrt α ^ 3)⁻¹ + Real.sqrt α ≤ (1 + κ₃ / 8) * (1 + α) := by
    have h1 : κ₃ / 8 * Real.sqrt α ≤ κ₃ / 8 * (1 + α) := mul_le_mul_of_nonneg_left hs1 (by positivity)
    nlinarith
  have hB : 2 / 3 * (Real.sqrt α ^ 3)⁻¹ ≤ κ₃ / 12 * (1 + α) := by
    have h1 : κ₃ / 8 * Real.sqrt α ≤ κ₃ / 8 * (1 + α) := mul_le_mul_of_nonneg_left hs1 (by positivity)
    nlinarith
  have hε4 : Real.exp (-(η / 4) * α) ≤ Real.exp (-(η / 8) * α) := Real.exp_le_exp.2 (by nlinarith)
  have hε8 : Real.exp (-(η / 8) * α) ≤ Real.exp (-(η / 8) * t₀) := Real.exp_le_exp.2 (by rw [hα]; nlinarith)
  have hP1 := exp_poly1 hη hαpos.le
  have hP8 := one_add_mul_exp_le (z := η / 8) (x := α) (by positivity) hαpos.le
  have e8 : 1 + 1 / (η / 8) = 1 + 8 / η := by field_simp
  rw [e8] at hP8
  have hE8 := Real.exp_pos (-(η / 8) * α)
  have hE4 := Real.exp_pos (-(η / 4) * α)
  have hE2 := Real.exp_pos (-(η / 2) * α)
  have hexp : Real.exp (-(η / 4) * α) = Real.exp (-(η / 8) * α) * Real.exp (-(η / 8) * α) := by
    rw [← Real.exp_add]; congr 1; ring
  -- first term
  have T1 : K / (c * k4) * (((Real.sqrt α ^ 3)⁻¹ + Real.sqrt α) * Real.exp (-(η / 2) * α)) ≤
      K / c * ((1 / k4) * (1 + κ₃ / 8) * (1 + 4 / η) * Real.exp (-(η / 8) * t₀)) := by
    have h1 : ((Real.sqrt α ^ 3)⁻¹ + Real.sqrt α) * Real.exp (-(η / 2) * α) ≤
        (1 + κ₃ / 8) * ((1 + 4 / η) * Real.exp (-(η / 4) * α)) := by
      calc _ ≤ ((1 + κ₃ / 8) * (1 + α)) * Real.exp (-(η / 2) * α) := mul_le_mul_of_nonneg_right hA hE2.le
        _ = (1 + κ₃ / 8) * ((1 + α) * Real.exp (-(η / 2) * α)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hP1 (by positivity)
    have h2 : (1 + κ₃ / 8) * ((1 + 4 / η) * Real.exp (-(η / 4) * α)) ≤
        (1 + κ₃ / 8) * ((1 + 4 / η) * Real.exp (-(η / 8) * t₀)) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hε4.trans hε8) (by positivity)) (by positivity)
    have hKc : 0 ≤ K / (c * k4) := by positivity
    calc _ ≤ K / (c * k4) * ((1 + κ₃ / 8) * ((1 + 4 / η) * Real.exp (-(η / 8) * t₀))) :=
          mul_le_mul_of_nonneg_left (h1.trans h2) hKc
      _ = _ := by field_simp
  -- second term
  have T2 : K * (1 + κ₃ / k4) / (c * k4) *
      (Real.exp (-(η / 4) * α) * (2 / 3 * (Real.sqrt α ^ 3)⁻¹ + cuspGam (η / 2))) ≤
      K / c * (((1 + κ₃ / k4) / k4) * (κ₃ / 12 * (1 + 8 / η) + cuspGam (η / 2)) * Real.exp (-(η / 8) * t₀)) := by
    have h1 : Real.exp (-(η / 4) * α) * (2 / 3 * (Real.sqrt α ^ 3)⁻¹ + cuspGam (η / 2)) ≤
        (κ₃ / 12 * (1 + 8 / η) + cuspGam (η / 2)) * Real.exp (-(η / 8) * t₀) := by
      have a1 : Real.exp (-(η / 4) * α) * (2 / 3 * (Real.sqrt α ^ 3)⁻¹) ≤
          Real.exp (-(η / 4) * α) * (κ₃ / 12 * (1 + α)) := mul_le_mul_of_nonneg_left hB hE4.le
      have a2 : (1 + α) * Real.exp (-(η / 4) * α) ≤ (1 + 8 / η) * Real.exp (-(η / 8) * α) := by
        rw [hexp]
        have := mul_le_mul_of_nonneg_right hP8 hE8.le
        calc (1 + α) * (Real.exp (-(η / 8) * α) * Real.exp (-(η / 8) * α)) =
            ((1 + α) * Real.exp (-(η / 8) * α)) * Real.exp (-(η / 8) * α) := by ring
          _ ≤ _ := this
      have a3 : Real.exp (-(η / 4) * α) * cuspGam (η / 2) ≤ Real.exp (-(η / 8) * t₀) * cuspGam (η / 2) :=
        mul_le_mul_of_nonneg_right (hε4.trans hε8) hΓ
      have a4 : Real.exp (-(η / 4) * α) * (κ₃ / 12 * (1 + α)) =
          κ₃ / 12 * ((1 + α) * Real.exp (-(η / 4) * α)) := by ring
      have a5 : κ₃ / 12 * ((1 + α) * Real.exp (-(η / 4) * α)) ≤
          κ₃ / 12 * ((1 + 8 / η) * Real.exp (-(η / 8) * t₀)) := by
        refine mul_le_mul_of_nonneg_left (a2.trans ?_) (by positivity)
        exact mul_le_mul_of_nonneg_left hε8 (by positivity)
      calc _ = Real.exp (-(η / 4) * α) * (2 / 3 * (Real.sqrt α ^ 3)⁻¹) + Real.exp (-(η / 4) * α) * cuspGam (η / 2) := by
            ring
        _ ≤ κ₃ / 12 * ((1 + 8 / η) * Real.exp (-(η / 8) * t₀)) + Real.exp (-(η / 8) * t₀) * cuspGam (η / 2) := by
            linarith
        _ = _ := by ring
    have hQ : 0 ≤ K * (1 + κ₃ / k4) / (c * k4) := by positivity
    calc _ ≤ K * (1 + κ₃ / k4) / (c * k4) *
          ((κ₃ / 12 * (1 + 8 / η) + cuspGam (η / 2)) * Real.exp (-(η / 8) * t₀)) :=
          mul_le_mul_of_nonneg_left h1 hQ
      _ = _ := by field_simp
  unfold cuspFarD4
  rw [← hk4, ← hκ₃]
  nlinarith [T1, T2]

end Tail

end FormalResearch.SignUncertainty.FctUnscaledCusp
