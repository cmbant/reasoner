/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctUnscaledCuspMidT0
public import FormalResearch.SignUncertainty.FctUnscaledCuspSetup

/-!
# `fct:unscaled-cusp`, regime `c^{-2/3} ≤ u ≤ 1`: elementary integrals and amplitude bounds (F2a)

Source: `CFT/sign_uncertainty/paper/constant_terms_five.tex`, Lemma `fct:unscaled-cusp`, second estimate.

Helper material for the three pieces `[0, t₀/2]`, `[t₀/2, 2t₀]`, `[2t₀, ∞)`: the amplitude bounds
`‖a x‖ ≤ K x^{1/2} e^{-ηx/2}`, `‖a' x‖ ≤ K x^{-1/2} e^{-ηx/2}` (`K = C_a M (e^η + 8/η²)`), and the elementary integrals
`∫_s^β x^{±1/2}`.

Class: proved.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped Real

namespace FormalResearch.SignUncertainty.FctUnscaledCusp

open FormalResearch.SignUncertainty FormalResearch.SignUncertainty.FctCuspEdge

section Common

variable {η Ca M : ℝ} {a : ℝ → ℂ}

/-- `‖a x‖ ≤ K x^{1/2} e^{-ηx/2}` on `x > 0`. -/
lemma CuspAmpPos.amp0 (ha : CuspAmpPos η Ca M a) (hη : 0 < η) (hCa : 0 ≤ Ca) (hM : 0 ≤ M) {x : ℝ} (hx : 0 < x) :
    ‖a x‖ ≤ Ca * M * ampC η * (x ^ ((1 : ℝ) / 2) * Real.exp (-(η / 2) * x)) := by
  have := ha.jet_le hη hCa hM (j := 0) (by norm_num) hx
  simpa [ampB] using this

/-- `‖a' x‖ ≤ K x^{-1/2} e^{-ηx/2}` on `x > 0`. -/
lemma CuspAmpPos.amp1 (ha : CuspAmpPos η Ca M a) (hη : 0 < η) (hCa : 0 ≤ Ca) (hM : 0 ≤ M) {x : ℝ} (hx : 0 < x) :
    ‖deriv a x‖ ≤ Ca * M * ampC η * (x ^ (-(1 : ℝ) / 2) * Real.exp (-(η / 2) * x)) := by
  have := ha.jet_le hη hCa hM (j := 1) (by norm_num) hx
  rw [iteratedDeriv_one] at this
  unfold ampB at this
  have e : (1 : ℝ) / 2 - ((1 : ℕ) : ℝ) = -(1 : ℝ) / 2 := by norm_num
  rw [e] at this
  exact this

lemma cuspK_nonneg (hη : 0 < η) (hCa : 0 ≤ Ca) (hM : 0 ≤ M) : 0 ≤ Ca * M * ampC η :=
  mul_nonneg (mul_nonneg hCa hM) (ampC_pos hη).le

end Common

/-! ### Elementary integrals -/

lemma sqrt_eq_rpow' (x : ℝ) : Real.sqrt x = x ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow x

/-- `∫_s^β x^{-1/2} = 2 (√β - √s)`. -/
lemma integral_isqrt {s β : ℝ} :
    ∫ x in s..β, x ^ (-(1 : ℝ) / 2) = 2 * (Real.sqrt β - Real.sqrt s) := by
  rw [integral_rpow (Or.inl (by norm_num))]
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, show -(1 : ℝ) / 2 + 1 = 1 / 2 by norm_num]
  ring

/-- `∫_s^β x^{1/2} = (2/3)(β^{3/2} - s^{3/2})`, with `β^{3/2} = (√β)³`. -/
lemma integral_sqrt_pow {s β : ℝ} (hs : 0 < s) (hsβ : s ≤ β) :
    ∫ x in s..β, x ^ ((1 : ℝ) / 2) = 2 / 3 * (Real.sqrt β ^ 3 - Real.sqrt s ^ 3) := by
  rw [integral_rpow (Or.inl (by norm_num))]
  have key : ∀ y : ℝ, 0 ≤ y → y ^ ((1 : ℝ) / 2 + 1) = Real.sqrt y ^ 3 := by
    intro y hy
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hy]
    norm_num
  rw [key _ (hs.le.trans hsβ), key _ hs.le]
  ring


/-! ### Piece 1: `[0, t₀/2]` -/

section Piece1

variable {𝔪 : ℝ → ℝ} {κ₁ κ₂ C₂ C₀ η Ca M : ℝ} {a : ℝ → ℂ}

/-- The constant of piece 1: `D₁ = 3/p₀ + κ₃/(3 p₀²)`, `p₀ = 3κ₁/(8 Tm)`. -/
noncomputable def cuspD1 (κ₁ κ₂ : ℝ) : ℝ :=
  3 / (3 * κ₁ / (8 * cuspTm κ₁)) + cuspK3 κ₂ / (3 * (3 * κ₁ / (8 * cuspTm κ₁)) ^ 2)

/-- **Piece 1** of the second estimate: `‖∫_0^{t₀/2} e^{icφ} a‖ ≤ K D₁ / (c r³)`, `r = √t₀`, `K = C_a M (e^η + 8/η²)`. -/
lemma cuspMid_piece1 (h : CuspPhase 𝔪 κ₁ κ₂ C₂ C₀) (ha : CuspAmpPos η Ca M a) (hη : 0 < η) (hCa : 0 ≤ Ca)
    (hM : 0 ≤ M) {c u r : ℝ} (hc : 0 < c) (hr : 0 < r) (hv : 𝔪 (r ^ 2) = u) (hu1 : u ≤ 1) :
    ‖∫ x in (0 : ℝ)..(r ^ 2 / 2), Complex.exp (Complex.I * ((c * cuspPhase 𝔪 u x : ℝ) : ℂ)) * a x‖ ≤
      Ca * M * ampC η * cuspD1 κ₁ κ₂ / (c * r ^ 3) := by
  have hκ := h.κ₁_pos
  have hκ3 := h.κ₃_pos
  have hTp := cuspTm_pos κ₁
  have ht₀ : 0 < r ^ 2 := by positivity
  set K : ℝ := Ca * M * ampC η with hK
  have hK0 : 0 ≤ K := cuspK_nonneg hη hCa hM
  set p0 : ℝ := 3 * κ₁ / (8 * cuspTm κ₁) with hp0
  have hp0pos : 0 < p0 := by positivity
  set g : ℝ := p0 * r ^ 4 with hg
  have hgpos : 0 < g := by positivity
  set p : ℝ := c * g with hp
  have hppos : 0 < p := by positivity
  set β : ℝ := r ^ 2 / 2 with hβ
  have hβpos : 0 < β := by positivity
  have hgap : ∀ x, 0 ≤ x → x ≤ β → g ≤ u - 𝔪 x := by
    intro x hx0 hx
    have := h.half_gap ht₀ hv hu1 hx0 hx
    have e : 3 * κ₁ * (r ^ 2) ^ 2 / (8 * cuspTm κ₁) = g := by rw [hg, hp0]; field_simp
    rwa [e] at this
  have hF : IntegrableOn (fun x => Complex.exp (Complex.I * ((c * cuspPhase 𝔪 u x : ℝ) : ℂ)) * a x) (Ioi 0) :=
    cuspF_integrableOn h.continuous ha hη hCa hM c u
  have hFi : IntervalIntegrable (fun x => Complex.exp (Complex.I * ((c * cuspPhase 𝔪 u x : ℝ) : ℂ)) * a x)
      volume 0 β := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hβpos.le]
    exact hF.mono_set Ioc_subset_Ioi_self
  have hamp0 : ∀ x, 0 < x → ‖a x‖ ≤ K * x ^ ((1 : ℝ) / 2) := by
    intro x hx
    refine (ha.amp0 hη hCa hM hx).trans ?_
    have : Real.exp (-(η / 2) * x) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    have h0 : 0 ≤ x ^ ((1 : ℝ) / 2) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left this h0]
  have hamp1 : ∀ x, 0 < x → ‖deriv a x‖ ≤ K * x ^ (-(1 : ℝ) / 2) := by
    intro x hx
    refine (ha.amp1 hη hCa hM hx).trans ?_
    have : Real.exp (-(η / 2) * x) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    have h0 : 0 ≤ x ^ (-(1 : ℝ) / 2) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left this h0]
  refine (norm_zero_le (A := K * cuspD1 κ₁ κ₂ / (c * r ^ 3)) (c₁ := K / p) (K := K) hβpos hFi
    (by positivity) hK0 ?_ ?_)
  · intro x hx
    rw [norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul, Real.sqrt_eq_rpow]
    exact hamp0 x hx.1
  · intro s hs
    obtain ⟨hs0, hsβ⟩ := hs
    have hib := cusp_ibp_one h ha hc hs0 hsβ (B0 := fun x => K * x ^ ((1 : ℝ) / 2))
      (B1 := fun x => K * x ^ (-(1 : ℝ) / 2)) (P1 := fun _ => p) (P2 := fun _ => c * cuspK3 κ₂ * β)
      (u := u) (fun x hx => hamp0 x (lt_of_lt_of_le hs0 hx.1))
      (fun x hx => hamp1 x (lt_of_lt_of_le hs0 hx.1))
      (fun x hx => ⟨hppos, by
        have := hgap x (hs0.le.trans hx.1) hx.2
        rw [abs_of_pos (by linarith [hgpos])]
        exact (mul_le_mul_of_nonneg_left this hc.le)⟩)
      (fun x hx => by
        have hx0 : 0 < x := lt_of_lt_of_le hs0 hx.1
        have h1 := h.deriv_le_w hx0
        have h2 := cuspW_le_self hx0.le
        have h3 : deriv 𝔪 x ≤ cuspK3 κ₂ * β :=
          h1.trans ((mul_le_mul_of_nonneg_left h2 hκ3.le).trans (mul_le_mul_of_nonneg_left hx.2 hκ3.le))
        calc c * deriv 𝔪 x ≤ c * (cuspK3 κ₂ * β) := mul_le_mul_of_nonneg_left h3 hc.le
          _ = c * cuspK3 κ₂ * β := by ring)
      (by
        have i1 : IntervalIntegrable (fun x : ℝ => x ^ (-(1 : ℝ) / 2)) volume s β :=
          intervalIntegral.intervalIntegrable_rpow' (by norm_num)
        have i2 : IntervalIntegrable (fun x : ℝ => x ^ ((1 : ℝ) / 2)) volume s β :=
          intervalIntegral.intervalIntegrable_rpow' (by norm_num)
        have := (i1.const_mul (K / p)).add (i2.const_mul (K * (c * cuspK3 κ₂ * β) / p ^ 2))
        refine this.congr ?_
        intro x _
        simp only
        ring)
    refine hib.trans ?_
    have i1 : IntervalIntegrable (fun x : ℝ => x ^ (-(1 : ℝ) / 2)) volume s β :=
      intervalIntegral.intervalIntegrable_rpow' (by norm_num)
    have i2 : IntervalIntegrable (fun x : ℝ => x ^ ((1 : ℝ) / 2)) volume s β :=
      intervalIntegral.intervalIntegrable_rpow' (by norm_num)
    have e1 : (∫ x in s..β, (K * x ^ (-(1 : ℝ) / 2) / p + K * x ^ ((1 : ℝ) / 2) * (c * cuspK3 κ₂ * β) / p ^ 2)) =
        K / p * (2 * (Real.sqrt β - Real.sqrt s)) +
          K * (c * cuspK3 κ₂ * β) / p ^ 2 * (2 / 3 * (Real.sqrt β ^ 3 - Real.sqrt s ^ 3)) := by
      have : (fun x : ℝ => K * x ^ (-(1 : ℝ) / 2) / p + K * x ^ ((1 : ℝ) / 2) * (c * cuspK3 κ₂ * β) / p ^ 2) =
          fun x => K / p * x ^ (-(1 : ℝ) / 2) + (K * (c * cuspK3 κ₂ * β) / p ^ 2) * x ^ ((1 : ℝ) / 2) := by
        funext x; ring
      rw [this, intervalIntegral.integral_add (i1.const_mul _) (i2.const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, integral_isqrt,
        integral_sqrt_pow hs0 hsβ]
    rw [e1, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
    set b : ℝ := Real.sqrt β with hb
    set sS : ℝ := Real.sqrt s with hsS
    have hb0 : 0 ≤ b := Real.sqrt_nonneg _
    have hsS0 : 0 ≤ sS := Real.sqrt_nonneg _
    have hbr : b ≤ r := by
      rw [hb, Real.sqrt_le_left hr.le]
      have : r ^ 2 / 2 ≤ r ^ 2 := by nlinarith [sq_nonneg r]
      exact this
    have hKp : 0 ≤ K / p := by positivity
    have hcr : 0 < c * r ^ 3 := by positivity
    have h1 : K / p * b + K / p * (2 * b) ≤ 3 * K / (c * p0 * r ^ 3) := by
      have : K / p * b + K / p * (2 * b) = K / p * (3 * b) := by ring
      rw [this]
      calc K / p * (3 * b) ≤ K / p * (3 * r) := by gcongr
        _ = 3 * K / (c * p0 * r ^ 3) := by rw [hp, hg]; field_simp
    have h2 : K * (c * cuspK3 κ₂ * β) / p ^ 2 * (2 / 3 * b ^ 3) ≤ K * cuspK3 κ₂ / (3 * c * p0 ^ 2 * r ^ 3) := by
      have hb3 : b ^ 3 ≤ r ^ 3 := pow_le_pow_left₀ hb0 hbr 3
      have hcoef : 0 ≤ K * (c * cuspK3 κ₂ * β) / p ^ 2 * (2 / 3) := by positivity
      calc K * (c * cuspK3 κ₂ * β) / p ^ 2 * (2 / 3 * b ^ 3)
          = K * (c * cuspK3 κ₂ * β) / p ^ 2 * (2 / 3) * b ^ 3 := by ring
        _ ≤ K * (c * cuspK3 κ₂ * β) / p ^ 2 * (2 / 3) * r ^ 3 := by gcongr
        _ = K * cuspK3 κ₂ / (3 * c * p0 ^ 2 * r ^ 3) := by rw [hp, hg, hβ]; field_simp
    have h3 : 0 ≤ K * (c * cuspK3 κ₂ * β) / p ^ 2 * (2 / 3 * sS ^ 3) := by positivity
    have h4 : 0 ≤ K / p * (2 * sS) := by positivity
    have hD : K * cuspD1 κ₁ κ₂ / (c * r ^ 3) =
        3 * K / (c * p0 * r ^ 3) + K * cuspK3 κ₂ / (3 * c * p0 ^ 2 * r ^ 3) := by
      unfold cuspD1; rw [← hp0]; field_simp
    rw [hD, mul_div_right_comm K b p, mul_div_right_comm K sS p]
    generalize K / p = A at *
    generalize K * (c * cuspK3 κ₂ * β) / p ^ 2 = X at *
    nlinarith [h1, h2, h3, h4]

/-! ### Piece 2: `[t₀/2, 2t₀]` -/

/-- The constant of piece 2: `D₂ = 40/√(κ₁/(8 Tm))`. -/
noncomputable def cuspD2 (κ₁ : ℝ) : ℝ := 40 / Real.sqrt (κ₁ / (8 * cuspTm κ₁))

/-- **Piece 2** of the second estimate (van der Corput on the saddle interval):
`‖∫_{t₀/2}^{2t₀} e^{icφ} a‖ ≤ K D₂ / √c`. -/
lemma cuspMid_piece2 (h : CuspPhase 𝔪 κ₁ κ₂ C₂ C₀) (ha : CuspAmpPos η Ca M a) (hη : 0 < η) (hCa : 0 ≤ Ca)
    (hM : 0 ≤ M) {c u r : ℝ} (hc : 0 < c) (hr : 0 < r) (hv : 𝔪 (r ^ 2) = u) (hu1 : u ≤ 1) :
    ‖∫ x in (r ^ 2 / 2)..(2 * r ^ 2), Complex.exp (Complex.I * ((c * cuspPhase 𝔪 u x : ℝ) : ℂ)) * a x‖ ≤
      Ca * M * ampC η * cuspD2 κ₁ / Real.sqrt c := by
  have hκ := h.κ₁_pos
  have hTp := cuspTm_pos κ₁
  have ht₀ : 0 < r ^ 2 := by positivity
  set K : ℝ := Ca * M * ampC η with hK
  have hK0 : 0 ≤ K := cuspK_nonneg hη hCa hM
  set q0 : ℝ := κ₁ / (8 * cuspTm κ₁) with hq0
  have hq0pos : 0 < q0 := by positivity
  set lam : ℝ := q0 * r ^ 2 with hlam
  have hlampos : 0 < lam := by positivity
  have hα : 0 < r ^ 2 / 2 := by positivity
  have hαβ : r ^ 2 / 2 ≤ 2 * r ^ 2 := by nlinarith [sq_nonneg r]
  have hsqx : ∀ x, r ^ 2 / 2 ≤ x → x ≤ 2 * r ^ 2 → Real.sqrt x ≤ 2 * r ∧ r / 2 ≤ Real.sqrt x := by
    intro x h1 h2
    constructor
    · rw [Real.sqrt_le_left (by positivity)]; nlinarith [sq_nonneg r]
    · apply Real.le_sqrt_of_sq_le; nlinarith [sq_nonneg r]
  have hM1 : ∀ x ∈ Icc (r ^ 2 / 2) (2 * r ^ 2), ‖a x‖ ≤ K * (2 * r) := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hα hx.1
    have h0 := ha.amp0 hη hCa hM hx0
    have he : Real.exp (-(η / 2) * x) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    have hs := (hsqx x hx.1 hx.2).1
    rw [← Real.sqrt_eq_rpow] at h0
    have h1 : Real.sqrt x * Real.exp (-(η / 2) * x) ≤ 2 * r := by
      have := Real.sqrt_nonneg x
      nlinarith [mul_le_mul_of_nonneg_left he this]
    exact h0.trans (mul_le_mul_of_nonneg_left h1 hK0)
  have hM2 : ∀ x ∈ Icc (r ^ 2 / 2) (2 * r ^ 2), ‖deriv a x‖ ≤ K * (2 / r) := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hα hx.1
    have h0 := ha.amp1 hη hCa hM hx0
    have he : Real.exp (-(η / 2) * x) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    have hs := (hsqx x hx.1 hx.2).2
    have e : x ^ (-(1 : ℝ) / 2) = (Real.sqrt x)⁻¹ := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hx0.le]; norm_num
    rw [e] at h0
    have h1 : (Real.sqrt x)⁻¹ * Real.exp (-(η / 2) * x) ≤ 2 / r := by
      have h2 : (Real.sqrt x)⁻¹ ≤ 2 / r := by
        rw [inv_le_comm₀ (Real.sqrt_pos.2 hx0) (by positivity)]
        rw [inv_div]; exact hs
      have h3 : 0 ≤ (Real.sqrt x)⁻¹ := by positivity
      nlinarith [mul_le_mul_of_nonneg_left he h3]
    exact h0.trans (mul_le_mul_of_nonneg_left h1 hK0)
  have hv2 := cusp_vdc h ha (η := η) (Ca := Ca) (M := M) (c := c) (u := u) hc hα hαβ hlampos
    (fun x hx => by
      have := h.mid_deriv ht₀ hv hu1 hx.1 hx.2
      calc lam = κ₁ * r ^ 2 / (8 * cuspTm κ₁) := by rw [hlam, hq0]; ring
        _ ≤ _ := this) hM1 hM2 (by positivity)
  refine hv2.trans (le_of_eq ?_)
  have hsq : Real.sqrt (c * lam) = Real.sqrt c * (r * Real.sqrt q0) := by
    rw [hlam, show c * (q0 * r ^ 2) = c * (r ^ 2 * q0) by ring, Real.sqrt_mul hc.le, Real.sqrt_mul (by positivity),
      Real.sqrt_sq hr.le]
  rw [hsq]
  unfold cuspD2
  rw [← hq0]
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  have hsq0 : 0 < Real.sqrt q0 := Real.sqrt_pos.2 hq0pos
  field_simp
  ring

end Piece1

end FormalResearch.SignUncertainty.FctUnscaledCusp
