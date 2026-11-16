module

public import FormalResearch.Special.AiryBiReal
public import FormalResearch.Special.AiryAsymReal

/-!
# `Bi'` on the negative axis with explicit error

Completes `AiryAsymReal`: for every `y > 0`, with `ξ = (2/3) y^{3/2}`,

* `airyBiDeriv_neg_asymptotic`  `|Bi'(-y) - π^{-1/2} y^{1/4} cos(ξ - π/4)| ≤ (2/5) y^{-5/4}`

(DLMF 9.7.12, first term, explicit remainder; the leading term is `π^{-1/2} y^{1/4} sin(ξ + π/4)`).
Same proof as `airyBi_neg_asymptotic`: the rotation `Bi'(z) = εω Ai'(ωz) + ε̄ω² Ai'(ω²z)` at `z = -r²`
is `2 Re(ε̄ω² Ai'(w²))` with `w = r e^{iπ/6}` (`ε̄ω² = e^{7πi/6}`), and `Ai'(w²)` is estimated by
`norm_deriv_airyAiC_sq_add_le`.  The constant `2/5` is that of `airyAi'_neg_asymptotic`
(numerically `|err| y^{5/4} ≤ 0.083`, mpmath over `y ∈ [10^{-4}, 10^4]`).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.Special

lemma conj_airyEps_mul_airyOmega_sq :
    (starRingEnd ℂ) airyEps * airyOmega ^ 2 = cexp (((7 * π / 6 : ℝ) : ℂ) * I) := by
  rw [conj_airyEps_eq_exp, airyOmega_sq_eq_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma airyBiDeriv_neg_eq (r : ℝ) :
    airyBiDeriv (-(r ^ 2)) = (((starRingEnd ℂ) ((starRingEnd ℂ) airyEps * airyOmega ^ 2)) *
      (starRingEnd ℂ) (deriv airyAiC (negW r ^ 2)) +
        ((starRingEnd ℂ) airyEps * airyOmega ^ 2) * deriv airyAiC (negW r ^ 2)).re := by
  have e1 : deriv airyAiC (airyOmega * ((-(r ^ 2) : ℝ) : ℂ)) =
      (starRingEnd ℂ) (deriv airyAiC (negW r ^ 2)) := by
    rw [← conj_negW_sq, conj_deriv_airyAiC]
  have e2 : deriv airyAiC (airyOmega ^ 2 * ((-(r ^ 2) : ℝ) : ℂ)) = deriv airyAiC (negW r ^ 2) := by
    rw [negW_sq]
  unfold airyBiDeriv airyBiC'
  rw [e1, e2]
  congr 1
  rw [map_mul, map_pow, Complex.conj_conj, conj_airyOmega, ← pow_mul]
  have h4 : airyOmega ^ (2 * 2) = airyOmega := by
    rw [show 2 * 2 = 3 + 1 by norm_num, pow_add, airyOmega_cube, one_mul, pow_one]
  rw [h4]
  ring_nf


lemma norm_conj_airyEps_mul_airyOmega_sq : ‖(starRingEnd ℂ) airyEps * airyOmega ^ 2‖ = 1 := by
  rw [conj_airyEps_mul_airyOmega_sq]; exact Complex.norm_exp_ofReal_mul_I _

lemma lead_real_Bi' {r : ℝ} (hr : 0 < r) :
    -(2 * (1 / (2 * π) * √(π / r) * r * Real.cos (7 * π / 6 + (-(2 / 3 * r ^ 3) + π / 12)))) =
      √r * Real.cos (2 / 3 * r ^ 3 - π / 4) / √π := by
  have e : Real.cos (7 * π / 6 + (-(2 / 3 * r ^ 3) + π / 12)) = -Real.cos (2 / 3 * r ^ 3 - π / 4) := by
    rw [show 7 * π / 6 + (-(2 / 3 * r ^ 3) + π / 12) = -((2 / 3 * r ^ 3 - π / 4) - π) by ring,
      Real.cos_neg, Real.cos_sub_pi]
  rw [e, Real.sqrt_div Real.pi_pos.le]
  have hπ : √π * √π = π := Real.mul_self_sqrt Real.pi_pos.le
  have hs : 0 < √r := Real.sqrt_pos.mpr hr
  have hsr : √r * √r = r := Real.mul_self_sqrt hr.le
  have hT : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
  generalize √π = T at hπ hT
  rw [← hπ]
  generalize √r = u at hsr hs ⊢
  rw [← hsr]
  field_simp

/-- **`Bi'` on the negative axis**, in the variable `r = √y`: for `r > 0`,
`|Bi'(-r²) - √r cos((2/3) r³ - π/4)/√π| ≤ 2/(5 √r r²)`. -/
theorem airyBiDeriv_neg_sq_asymptotic {r : ℝ} (hr : 0 < r) :
    |airyBiDeriv (-(r ^ 2)) - √r * Real.cos (2 / 3 * r ^ 3 - π / 4) / √π| ≤ 2 / (5 * (√r * r ^ 2)) := by
  set A := deriv airyAiC (negW r ^ 2) with hA
  set L : ℂ := -(((1 / (2 * π) * √(π / r) * r : ℝ) : ℂ) *
    cexp (((-(2 / 3 * r ^ 3) + π / 12 : ℝ) : ℂ) * I)) with hL
  have h1 := abs_two_re_sub_le norm_conj_airyEps_mul_airyOmega_sq A L
  have h2 : (((starRingEnd ℂ) airyEps * airyOmega ^ 2) * L).re =
      -(1 / (2 * π) * √(π / r) * r * Real.cos (7 * π / 6 + (-(2 / 3 * r ^ 3) + π / 12))) := by
    rw [hL, mul_neg, Complex.neg_re, conj_airyEps_mul_airyOmega_sq]
    rw [re_exp_mul_exp]
  have h3 : airyBiDeriv (-(r ^ 2)) - √r * Real.cos (2 / 3 * r ^ 3 - π / 4) / √π =
      (((starRingEnd ℂ) ((starRingEnd ℂ) airyEps * airyOmega ^ 2) * (starRingEnd ℂ) A +
        ((starRingEnd ℂ) airyEps * airyOmega ^ 2) * A).re -
        2 * (((starRingEnd ℂ) airyEps * airyOmega ^ 2) * L).re) := by
    have := lead_real_Bi' hr
    rw [airyBiDeriv_neg_eq, h2, ← this]; ring
  rw [h3]
  have h4 : ‖A - L‖ ≤ 1 / (5 * (√r * r ^ 2)) := by
    have := norm_deriv_airyAiC_negW_add_le hr
    rw [hL, sub_neg_eq_add]
    exact this
  calc _ ≤ 2 * ‖A - L‖ := h1
    _ ≤ 2 * (1 / (5 * (√r * r ^ 2))) := by gcongr
    _ = 2 / (5 * (√r * r ^ 2)) := by ring

/-- **DLMF 9.7.12 with explicit remainder**: for every `y > 0`,
`|Bi'(-y) - π^{-1/2} y^{1/4} cos((2/3) y^{3/2} - π/4)| ≤ (2/5) y^{-5/4}`. -/
theorem airyBiDeriv_neg_asymptotic {y : ℝ} (hy : 0 < y) :
    |airyBiDeriv (-y) - 1 / √π * y ^ (1 / 4 : ℝ) * Real.cos (2 / 3 * y ^ (3 / 2 : ℝ) - π / 4)| ≤
      2 / 5 * y ^ (-(5 / 4) : ℝ) := by
  have hr : 0 < √y := Real.sqrt_pos.mpr hy
  have h := airyBiDeriv_neg_sq_asymptotic hr
  rw [Real.sq_sqrt hy.le] at h
  have hT : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
  have e1 : 1 / √π * y ^ (1 / 4 : ℝ) * Real.cos (2 / 3 * y ^ (3 / 2 : ℝ) - π / 4) =
      √(√y) * Real.cos (2 / 3 * (√y) ^ 3 - π / 4) / √π := by
    rw [← sqrt_sqrt_eq_rpow hy, ← sqrt_cube_eq_rpow hy]
    field_simp
  rw [e1, rpow_neg_five_quarter hy, Real.sq_sqrt hy.le]
  convert h using 2
  have hs : 0 < √(√y) := Real.sqrt_pos.mpr hr
  field_simp

/-- info: 'FormalResearch.Special.airyBiDeriv_neg_asymptotic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyBiDeriv_neg_asymptotic

end FormalResearch.Special
