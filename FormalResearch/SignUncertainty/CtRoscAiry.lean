module

public import Mathlib
public import FormalResearch.Special.AiryRplusAsym
public import FormalResearch.SignUncertainty.CtRoscUpper
public import FormalResearch.SignUncertainty.CtDyadicEta

/-!
# `(ct:rosc)`: the Airy comparison `R₊ ≈ 2E` on the upper semicircle at good radii

`constant_terms_lower.tex`, proof of `(ct:rosc)`: on the upper semicircle `w = Re^{iθ}`, `θ ∈ [0, π]`, of a good radius `R`,
`‖W₆(w)‖ ‖R₊(w) - 2E(w)‖ ≤ C R^{-3/2} ‖E(w)‖` with `W₆(w) = (1-(w/R)^{12})²`, `R₊ = (Bi - iAi)/Ai`, `E = airyUpE` (`AiryRplusComparison`).

Proof (`airyRplusComparison`), with `R = σ⁴`:
* `Re w ≥ -R/2`: `airyRplus_sub_two_exp_mid` (sector asymptotics of `Ai(w)` and `Ai(ω²w)`, DLMF 9.7.5), `‖W₆‖ ≤ 4`;
* `Re w < -R/2`, `Im w ≥ 2σ`: `‖E‖ ≤ R^{-3/2}` (`airyRp_norm_exp_le`) and `airyRplus_sub_two_exp_neg` (the rotation identity), `‖W₆‖ ≤ 4`;
* `Re w < -R/2`, `Im w < 2σ` (within angle `π-θ < πR^{-3/4}` of the negative axis): the good-radius bound `airy_Rplus_bound`
  `‖R₊‖ ≤ 30√π ‖E‖` and `‖W₆‖ ≤ (12(π-θ))² ≤ 144π² R^{-3/2}`.
The constant is `C = 144π²(30√π + 2) + 96`, `R₀ = 4`.  The paper's split at `φ₀ = 2R^{-3/2} log R` (DLMF 9.7.9 on `φ ≥ φ₀`) is replaced by the
split at `π - θ ≈ R^{-3/4}`, where `W₆ = O(R^{-3/2})` already, so the two-exponential form of `Ai` near the negative axis is never needed.
All proved.
-/

@[expose] public section

open Complex Set
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.Special

/-- **`AiryRplusComparison`** (pure Airy asymptotics, `ap:thmD`, DLMF 9.7.5): at good radii the reflection function
`R₊ = (Bi - iAi)/Ai` of the upper semicircle is `2 e^{(4/3)u^{3/2}}` up to relative error `O(R^{-3/2})`, tapered by `W₆`:
`‖W₆(w)‖ ‖R₊(w) - 2E(w)‖ ≤ C R^{-3/2} ‖E(w)‖` on `w = Re^{iθ}`, `θ ∈ [0, π]`, with `W₆(w) = (1-(w/R)^{12})²`.  Numerically `C ≈ 1.67`
(scratch check `R ∈ [10, 400]`, good radii); proved with `C = 144π²(30√π+2) + 96` (`airyRplusComparison`). -/
def AiryRplusComparison : Prop :=
  ∃ C R₀ : ℝ, 0 ≤ C ∧ ∀ R : ℝ, R₀ ≤ R → ctGoodRadius R → ∀ θ ∈ Icc (0 : ℝ) π,
    ‖(1 - (circleMap 0 R θ / (R : ℂ)) ^ 12) ^ 2‖ * ‖airyRplus (circleMap 0 R θ) - 2 * airyUpE (circleMap 0 R θ)‖ ≤
      C * R ^ (-(3 / 2 : ℝ)) * ‖airyUpE (circleMap 0 R θ)‖

lemma airyUpE_eq_cexp {u : ℂ} (hu : 0 ≤ u.im) (h0 : u ≠ 0) :
    airyUpE u = Complex.exp ((4 / 3 : ℂ) * u ^ (3 / 2 : ℂ)) := by
  unfold airyUpE; rw [airyUp_pow_eq hu h0]

lemma circleMap_div_eq {R θ : ℝ} (hR : R ≠ 0) :
    (circleMap 0 R θ / (R : ℂ)) ^ 12 = Complex.exp (I * ((12 * θ : ℝ) : ℂ)) := by
  rw [circleMap_zero, mul_div_cancel_left₀ _ (by exact_mod_cast hR), ← Complex.exp_nat_mul]
  congr 1; push_cast; ring

lemma ctW6_norm_le_four (R θ : ℝ) (hR : R ≠ 0) : ‖(1 - (circleMap 0 R θ / (R : ℂ)) ^ 12) ^ 2‖ ≤ 4 := by
  rw [norm_pow, circleMap_div_eq hR]
  have h : ‖1 - Complex.exp (I * ((12 * θ : ℝ) : ℂ))‖ ≤ 2 := by
    calc _ ≤ ‖(1 : ℂ)‖ + ‖Complex.exp (I * ((12 * θ : ℝ) : ℂ))‖ := norm_sub_le _ _
      _ = 2 := by rw [Complex.norm_exp_I_mul_ofReal]; norm_num
  nlinarith [norm_nonneg (1 - Complex.exp (I * ((12 * θ : ℝ) : ℂ)))]

lemma ctW6_norm_le_near (R θ : ℝ) (hR : R ≠ 0) (hθ : θ ≤ π) :
    ‖(1 - (circleMap 0 R θ / (R : ℂ)) ^ 12) ^ 2‖ ≤ (12 * (π - θ)) ^ 2 := by
  rw [norm_pow, circleMap_div_eq hR]
  have e : Complex.exp (I * ((12 * θ : ℝ) : ℂ)) = Complex.exp (I * ((12 * (θ - π) : ℝ) : ℂ)) := by
    have : I * ((12 * θ : ℝ) : ℂ) = I * ((12 * (θ - π) : ℝ) : ℂ) + (6 : ℕ) * (2 * π * I) := by
      push_cast; ring
    rw [this, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := 12 * (θ - π))
  rw [e, norm_sub_rev]
  have h2 : ‖((12 * (θ - π) : ℝ))‖ = 12 * (π - θ) := by
    rw [Real.norm_eq_abs, abs_of_nonpos (by linarith)]; ring
  rw [h2] at h
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

/-- **`AiryRplusComparison` holds** (`(ct:rosc)`, DLMF 9.7.5 + the good-radius bound): `C = 144π²(30√π+2) + 96`, `R₀ = 4`. -/
theorem airyRplusComparison : AiryRplusComparison := by
  refine ⟨144 * π ^ 2 * (30 * √π + 2) + 96, 4, by positivity, ?_⟩
  intro R hR4 hgood θ hθ
  have hR0 : 0 < R := by linarith
  set u := circleMap 0 R θ with hudef
  have hun : ‖u‖ = R := by rw [hudef, norm_circleMap_zero, abs_of_pos hR0]
  have hure : u.re = R * Real.cos θ := by simp [hudef, circleMap_zero, Complex.exp_re]
  have huim : u.im = R * Real.sin θ := by simp [hudef, circleMap_zero, Complex.exp_im]
  have hsin : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 hθ.2
  have hu : 0 ≤ u.im := by rw [huim]; positivity
  have h0 : u ≠ 0 := by intro h; rw [h, norm_zero] at hun; linarith
  -- `R = σ⁴`
  set σ := R ^ (1 / 4 : ℝ) with hσdef
  have hσ : 0 < σ := Real.rpow_pos_of_pos hR0 _
  have hRσ : R = σ ^ 4 := by
    rw [hσdef, ← Real.rpow_natCast, ← Real.rpow_mul hR0.le]; norm_num
  have hsq : √R = σ ^ 2 := by
    rw [hRσ, show σ ^ 4 = (σ ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have h32 : R ^ (3 / 2 : ℝ) = σ ^ 6 := by
    rw [airyRpow_three_halves_eq hR0, hsq, hRσ]; ring
  have hρ : R ^ (-(3 / 2 : ℝ)) = (σ ^ 6)⁻¹ := by rw [Real.rpow_neg hR0.le, h32]
  have h8 : 8 ≤ ‖u‖ ^ (3 / 2 : ℝ) := by
    rw [hun, airyRpow_three_halves_eq hR0]
    have : 2 ≤ √R := Real.le_sqrt_of_sq_le (by linarith)
    nlinarith
  have hE := airyUpE_eq_cexp hu h0
  have hRp : airyRplus u = (airyBiC u - I * airyAiC u) / airyAiC u := rfl
  rw [hRp, hE]
  set E := Complex.exp ((4 / 3 : ℂ) * u ^ (3 / 2 : ℂ)) with hEdef
  set ρ := R ^ (-(3 / 2 : ℝ)) with hρdef
  have hρ0 : 0 ≤ ρ := Real.rpow_nonneg hR0.le _
  have hEn := norm_nonneg E
  have hW4 := ctW6_norm_le_four R θ hR0.ne'
  have hWn := norm_nonneg ((1 - (u / (R : ℂ)) ^ 12) ^ 2)
  have hπ := Real.pi_pos
  have hC : 96 ≤ 144 * π ^ 2 * (30 * √π + 2) + 96 := by
    have : 0 ≤ 144 * π ^ 2 * (30 * √π + 2) := by positivity
    linarith
  by_cases hmid : -(‖u‖ / 2) ≤ u.re
  · have hX := airyRplus_sub_two_exp_mid hu hmid h8
    rw [hun] at hX
    calc _ ≤ 4 * (16 * ρ * ‖E‖) := mul_le_mul hW4 hX (norm_nonneg _) (by norm_num)
      _ ≤ _ := by
        have hk := mul_nonneg hρ0 hEn
        nlinarith only [hk, mul_le_mul_of_nonneg_right hC hk]
  push Not at hmid
  by_cases hy : 2 * σ ≤ u.im
  · have hEs := airyRp_norm_exp_le hσ (by rw [hun, hRσ]) hu hmid.le hy
    have hX := airyRplus_sub_two_exp_neg hu hmid.le (by rw [hun]; show ‖E‖ ≤ ρ; rw [hρ]; exact hEs) h8
    rw [hun] at hX
    calc _ ≤ 4 * (24 * ρ * ‖E‖) := mul_le_mul hW4 hX (norm_nonneg _) (by norm_num)
      _ ≤ _ := by
        have hk := mul_nonneg hρ0 hEn
        nlinarith only [hk, mul_le_mul_of_nonneg_right hC hk]
  push Not at hy
  -- near the negative axis: crude good-radius bound and a small taper
  have hg := hgood u hun
  rw [← hun] at hg
  have hcr := airy_Rplus_bound hu hg
  have hEnv : ‖E‖ = (airyEnv u)⁻¹ := by rw [← norm_airyUpE hu, hE]
  have henv := airyEnv_pos u
  have hR1 : ‖(airyBiC u - I * airyAiC u) / airyAiC u‖ ≤ 30 * √π * ‖E‖ := by
    rw [hEnv, ← div_eq_mul_inv, le_div_iff₀ henv]; exact hcr
  have hX : ‖(airyBiC u - I * airyAiC u) / airyAiC u - 2 * E‖ ≤ (30 * √π + 2) * ‖E‖ := by
    calc _ ≤ ‖(airyBiC u - I * airyAiC u) / airyAiC u‖ + ‖2 * E‖ := norm_sub_le _ _
      _ ≤ 30 * √π * ‖E‖ + 2 * ‖E‖ := by
        have : ‖(2 : ℂ) * E‖ = 2 * ‖E‖ := by rw [norm_mul]; norm_num
        linarith
      _ = _ := by ring
  -- the angle `s = π - θ` is small
  have hcos : Real.cos θ < 0 := by
    rw [hun, hure] at hmid
    by_contra hc
    push Not at hc
    have := mul_nonneg hR0.le hc
    linarith
  have hθ2 : π / 2 < θ := by
    by_contra hc; push Not at hc
    have := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1], hc⟩
    linarith
  have hs0 : 0 ≤ π - θ := by linarith [hθ.2]
  have hJ := Real.mul_le_sin hs0 (by linarith)
  rw [Real.sin_pi_sub] at hJ
  have hsinσ : R * Real.sin θ < 2 * σ := by rw [← huim]; exact hy
  have hs : π - θ ≤ π / σ ^ 3 := by
    rw [hRσ] at hsinσ
    have h1 : σ ^ 3 * Real.sin θ < 2 := by
      have : σ * (σ ^ 3 * Real.sin θ) < σ * 2 := by
        have e : σ * (σ ^ 3 * Real.sin θ) = σ ^ 4 * Real.sin θ := by ring
        rw [e]; linarith
      exact lt_of_mul_lt_mul_left this hσ.le
    have h2 : π - θ ≤ π / 2 * Real.sin θ := by
      calc π - θ = π / 2 * (2 / π * (π - θ)) := by field_simp
        _ ≤ π / 2 * Real.sin θ := by gcongr
    have h3 : Real.sin θ ≤ 2 / σ ^ 3 := by
      rw [le_div_iff₀ (by positivity)]; linarith
    calc π - θ ≤ π / 2 * Real.sin θ := h2
      _ ≤ π / 2 * (2 / σ ^ 3) := by gcongr
      _ = π / σ ^ 3 := by field_simp
  have hW := ctW6_norm_le_near R θ hR0.ne' hθ.2
  have hW' : ‖(1 - (u / (R : ℂ)) ^ 12) ^ 2‖ ≤ 144 * π ^ 2 * ρ := by
    refine hW.trans ?_
    show _ ≤ 144 * π ^ 2 * ρ
    rw [hρ]
    have : (12 * (π - θ)) ^ 2 ≤ (12 * (π / σ ^ 3)) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
    refine this.trans (le_of_eq ?_)
    field_simp
    norm_num
  have hk : 0 ≤ 30 * √π + 2 := by positivity
  calc _ ≤ 144 * π ^ 2 * ρ * ((30 * √π + 2) * ‖E‖) := mul_le_mul hW' hX (norm_nonneg _) (by positivity)
    _ = 144 * π ^ 2 * (30 * √π + 2) * (ρ * ‖E‖) := by ring
    _ ≤ (144 * π ^ 2 * (30 * √π + 2) + 96) * (ρ * ‖E‖) :=
        mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hρ0 hEn)
    _ = _ := by ring

/-- info: 'FormalResearch.SignUncertainty.airyRplusComparison' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms airyRplusComparison

end FormalResearch.SignUncertainty
