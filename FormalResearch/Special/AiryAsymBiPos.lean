module

public import FormalResearch.Special.AiryAsymBiNeg
public import FormalResearch.Special.AiryAsymPos

/-!
# `Bi` and `Bi'` on the positive axis with explicit error

For every `x > 0`, with `ξ = (2/3) x^{3/2}`:

* `airyBi_pos_asymptotic`       `|Bi(x) - π^{-1/2} x^{-1/4} e^{ξ}| ≤ (4/5) x^{-7/4} e^{ξ}`,
* `airyBiDeriv_pos_asymptotic`  `|Bi'(x) - π^{-1/2} x^{1/4} e^{ξ}| ≤ (7/4) x^{-5/4} e^{ξ}`

(DLMF 9.7.7, 9.7.8, first term, explicit remainder: relative error `O(x^{-3/2})`; `Bi` is the dominant solution).
Proof: `Bi(z) = ε Ai(ωz) + ε̄ Ai(ω²z)`; at `z = r²` (`r = √x`) one has `ωz = w²`, `ω²z = conj(w²)` with
`w = r e^{iπ/3}` (`Re w = r/2 > 0`, `w³ = -r³`, so `e^{-(2/3)w³} = e^{ξ}` is real and large), hence
`Bi(r²) = 2 Re(ε Ai(w²))` and `Bi'(r²) = 2 Re(εω Ai'(w²))`; the leading terms `ε (π/w)^{1/2} e^{ξ}/2π`,
`-εω w (π/w)^{1/2} e^{ξ}/2π` are real, and the second-order saddle estimates of `AiryAsymSaddle`
(with `ρ = r/2`) bound the rest.  Constants are those of the proof; numerically (mpmath, `x ∈ [10^{-4}, 10^{4}]`)
`|err| x^{7/4} e^{-ξ} ≤ 0.089` and `|err| x^{5/4} e^{-ξ} ≤ 0.119`.

Not formalised: higher terms of the expansion.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.Special

/-- The saddle `w = r e^{iπ/3}` for `Bi(r²)`: `w² = ω r²`, `w³ = -r³`, `Re w = r/2`. -/
noncomputable def biW (r : ℝ) : ℂ := (r : ℂ) * cexp (((π / 3 : ℝ) : ℂ) * I)

lemma re_biW (r : ℝ) : (biW r).re = r / 2 := by
  unfold biW
  rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re, Real.cos_pi_div_three]
  ring

lemma biW_sq (r : ℝ) : biW r ^ 2 = airyOmega * ((r ^ 2 : ℝ) : ℂ) := by
  unfold biW
  rw [mul_pow, ← Complex.exp_nat_mul, airyOmega_eq_exp']
  push_cast
  rw [show ((2 : ℂ) * ((π : ℂ) / 3 * I)) = (2 * π / 3 : ℂ) * I by ring]
  ring

lemma conj_biW_sq (r : ℝ) : (starRingEnd ℂ) (biW r ^ 2) = airyOmega ^ 2 * ((r ^ 2 : ℝ) : ℂ) := by
  rw [biW_sq, map_mul, conj_airyOmega, Complex.conj_ofReal]

lemma biW_cube (r : ℝ) : biW r ^ 3 = ((-(r ^ 3) : ℝ) : ℂ) := by
  unfold biW
  rw [mul_pow, ← Complex.exp_nat_mul]
  have : ((3 : ℕ) : ℂ) * (((π / 3 : ℝ) : ℂ) * I) = π * I := by push_cast; ring
  rw [this, Complex.exp_pi_mul_I]
  push_cast; ring

lemma exp_biW_cube (r : ℝ) :
    cexp (-(2 / 3) * biW r ^ 3) = ((Real.exp (2 / 3 * r ^ 3) : ℝ) : ℂ) := by
  rw [biW_cube, Complex.ofReal_exp]
  congr 1
  push_cast
  ring

lemma norm_exp_biW_cube (r : ℝ) : ‖cexp (-(2 / 3) * biW r ^ 3)‖ = Real.exp (2 / 3 * r ^ 3) := by
  rw [exp_biW_cube, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

lemma norm_biW (r : ℝ) (hr : 0 < r) : ‖biW r‖ = r := by
  unfold biW
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, Complex.norm_exp_ofReal_mul_I,
    mul_one]

lemma sqrt_pi_div_biW {r : ℝ} (hr : 0 < r) :
    ((π : ℂ) / biW r) ^ (1 / 2 : ℂ) =
      ((√(π / r) : ℝ) : ℂ) * cexp (((-(π / 6) : ℝ) : ℂ) * I) := by
  have hw : 0 < (biW r).re := by rw [re_biW]; positivity
  have hb2 : (((√(π / r) : ℝ) : ℂ) * cexp (((-(π / 6) : ℝ) : ℂ) * I)) ^ 2 = π / biW r := by
    unfold biW
    rw [mul_pow, ← Complex.exp_nat_mul, ← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
    have : cexp (((2 : ℕ) : ℂ) * (((-(π / 6) : ℝ) : ℂ) * I)) =
        (cexp (((π / 3 : ℝ) : ℂ) * I))⁻¹ := by
      rw [← Complex.exp_neg]; congr 1; push_cast; ring
    rw [this]
    push_cast
    have : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    field_simp
  have hbre : 0 < (((√(π / r) : ℝ) : ℂ) * cexp (((-(π / 6) : ℝ) : ℂ) * I)).re := by
    rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
    refine mul_pos (Real.sqrt_pos.mpr (by positivity)) (Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩)
    · linarith [Real.pi_pos]
    · linarith [Real.pi_pos]
  apply eq_of_sq_eq_of_re_pos
  · rw [hb2]
    simp
  · exact re_cpow_half_pos (re_div_pos hw)
  · exact hbre


/-! ### Rotation identities at `z = r²` -/

lemma airyBi_pos_eq (r : ℝ) :
    airyBi (r ^ 2) = (((starRingEnd ℂ) airyEps * (starRingEnd ℂ) (airyAiC (biW r ^ 2))) +
      airyEps * airyAiC (biW r ^ 2)).re := by
  have e1 : airyAiC (airyOmega * ((r ^ 2 : ℝ) : ℂ)) = airyAiC (biW r ^ 2) := by rw [biW_sq]
  have e2 : airyAiC (airyOmega ^ 2 * ((r ^ 2 : ℝ) : ℂ)) = (starRingEnd ℂ) (airyAiC (biW r ^ 2)) := by
    rw [← conj_biW_sq, conj_airyAiC]
  unfold airyBi airyBiC
  rw [e1, e2]
  congr 1
  ring

lemma airyBiDeriv_pos_eq (r : ℝ) :
    airyBiDeriv (r ^ 2) = (((starRingEnd ℂ) (airyEps * airyOmega) *
      (starRingEnd ℂ) (deriv airyAiC (biW r ^ 2))) + (airyEps * airyOmega) *
        deriv airyAiC (biW r ^ 2)).re := by
  have e1 : deriv airyAiC (airyOmega * ((r ^ 2 : ℝ) : ℂ)) = deriv airyAiC (biW r ^ 2) := by
    rw [biW_sq]
  have e2 : deriv airyAiC (airyOmega ^ 2 * ((r ^ 2 : ℝ) : ℂ)) =
      (starRingEnd ℂ) (deriv airyAiC (biW r ^ 2)) := by
    rw [← conj_biW_sq, conj_deriv_airyAiC]
  unfold airyBiDeriv airyBiC'
  rw [e1, e2]
  congr 1
  rw [map_mul, conj_airyOmega]
  ring

/-! ### The leading terms -/

lemma lead_biAi {r : ℝ} (hr : 0 < r) :
    (1 / (2 * (π : ℂ))) * cexp (-(2 / 3) * biW r ^ 3) * (π / biW r) ^ (1 / 2 : ℂ) =
      ((1 / (2 * π) * √(π / r) * Real.exp (2 / 3 * r ^ 3) : ℝ) : ℂ) *
        cexp (((-(π / 6) : ℝ) : ℂ) * I) := by
  rw [exp_biW_cube, sqrt_pi_div_biW hr]
  push_cast
  ring

/-- `-Ai'(w²)` leading term: `(1/2π) e^{-(2/3)w³} w (π/w)^{1/2}` has modulus `(1/2π) √(πr) e^{ξ}` and phase `π/6`. -/
lemma lead_biAi' {r : ℝ} (hr : 0 < r) :
    (1 / (2 * (π : ℂ))) * cexp (-(2 / 3) * biW r ^ 3) * (biW r * (π / biW r) ^ (1 / 2 : ℂ)) =
      ((1 / (2 * π) * √(π / r) * r * Real.exp (2 / 3 * r ^ 3) : ℝ) : ℂ) *
        cexp (((π / 6 : ℝ) : ℂ) * I) := by
  rw [exp_biW_cube, sqrt_pi_div_biW hr]
  unfold biW
  have : cexp (((π / 3 : ℝ) : ℂ) * I) = cexp (((π / 6 : ℝ) : ℂ) * I) *
      cexp (((π / 6 : ℝ) : ℂ) * I) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [this]
  have h2 : cexp (((π / 6 : ℝ) : ℂ) * I) * cexp (((-(π / 6) : ℝ) : ℂ) * I) = 1 := by
    rw [← Complex.exp_add]; simp
  generalize cexp (((π / 6 : ℝ) : ℂ) * I) = E at h2 ⊢
  generalize cexp (((-(π / 6) : ℝ) : ℂ) * I) = F at h2 ⊢
  push_cast
  linear_combination (1 / (2 * (π : ℂ)) * cexp (2 / 3 * (r : ℂ) ^ 3) * ((√(π / r) : ℝ) : ℂ) * r *
    E) * h2


/-! ### Constants -/

lemma biPos_err0 {r : ℝ} (hr : 0 < r) :
    1 / (2 * π) * (5 / 48 * (√(π / (r / 2)) / (r / 2) ^ 3)) ≤ 2 / 5 * (1 / (√r * r ^ 3)) := by
  have hs : 0 < √r := Real.sqrt_pos.mpr hr
  have hT := sqrtpi_ge
  have hπ : √π * √π = π := Real.mul_self_sqrt Real.pi_pos.le
  have hq : √(2 : ℝ) * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hq0 : 0 ≤ √(2 : ℝ) := Real.sqrt_nonneg _
  have hq1 : √(2 : ℝ) ≤ 3 / 2 := by nlinarith
  have hsr : √r * √r = r := Real.mul_self_sqrt hr.le
  have e : √(π / (r / 2)) = √2 * √π / √r := by
    rw [show π / (r / 2) = 2 * π / r by field_simp, Real.sqrt_div (by positivity),
      Real.sqrt_mul (by norm_num)]
  rw [e]
  have hT0 : 0 < √π := by linarith
  generalize √π = T at hπ hT hT0 ⊢
  generalize √(2 : ℝ) = q at hq hq0 hq1 ⊢
  generalize √r = u at hsr hs ⊢
  rw [← hπ]
  subst hsr
  have hu : 0 < u * u := by positivity
  have e2 : 1 / (2 * (T * T)) * (5 / 48 * (q * T / u / (u * u / 2) ^ 3)) =
      (5 * q / (12 * T)) * (1 / (u * (u * u) ^ 3)) := by
    field_simp
    ring
  rw [e2]
  have : 5 * q / (12 * T) ≤ 2 / 5 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  exact mul_le_mul_of_nonneg_right this (by positivity)

lemma biPos_err1 {r : ℝ} (hr : 0 < r) :
    1 / (2 * π) * (r * (5 / 48 * (√(π / (r / 2)) / (r / 2) ^ 3)) + 1 / 4 * (√(π / (r / 2)) / (r / 2) ^ 2)) ≤
      7 / 8 * (1 / (√r * r ^ 2)) := by
  have hs : 0 < √r := Real.sqrt_pos.mpr hr
  have hT := sqrtpi_ge
  have hπ : √π * √π = π := Real.mul_self_sqrt Real.pi_pos.le
  have hq : √(2 : ℝ) * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hq0 : 0 ≤ √(2 : ℝ) := Real.sqrt_nonneg _
  have hq1 : √(2 : ℝ) ≤ 3 / 2 := by nlinarith
  have hsr : √r * √r = r := Real.mul_self_sqrt hr.le
  have e : √(π / (r / 2)) = √2 * √π / √r := by
    rw [show π / (r / 2) = 2 * π / r by field_simp, Real.sqrt_div (by positivity),
      Real.sqrt_mul (by norm_num)]
  rw [e]
  have hT0 : 0 < √π := by linarith
  generalize √π = T at hπ hT hT0 ⊢
  generalize √(2 : ℝ) = q at hq hq0 hq1 ⊢
  generalize √r = u at hsr hs ⊢
  rw [← hπ]
  subst hsr
  have hu : 0 < u * u := by positivity
  have e2 : 1 / (2 * (T * T)) * (u * u * (5 / 48 * (q * T / u / (u * u / 2) ^ 3)) +
      1 / 4 * (q * T / u / (u * u / 2) ^ 2)) = (11 * q / (12 * T)) * (1 / (u * (u * u) ^ 2)) := by
    field_simp
    ring
  rw [e2]
  have : 11 * q / (12 * T) ≤ 7 / 8 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  exact mul_le_mul_of_nonneg_right this (by positivity)

lemma norm_airyEps_mul_airyOmega : ‖airyEps * airyOmega‖ = 1 := by
  rw [norm_mul, norm_airyEps, norm_airyOmega, mul_one]

lemma airyEps_mul_airyOmega_eq : airyEps * airyOmega = cexp (((5 * π / 6 : ℝ) : ℂ) * I) := by
  rw [airyEps_eq_exp', airyOmega_eq_exp', ← Complex.exp_add]
  congr 1
  push_cast
  ring


lemma lead_real_BiPos {r : ℝ} (hr : 0 < r) :
    2 * (1 / (2 * π) * √(π / r) * Real.exp (2 / 3 * r ^ 3) * Real.cos (π / 6 + (-(π / 6)))) =
      Real.exp (2 / 3 * r ^ 3) / (√π * √r) := by
  rw [show π / 6 + (-(π / 6)) = 0 by ring, Real.cos_zero, Real.sqrt_div Real.pi_pos.le]
  have hπ : √π * √π = π := Real.mul_self_sqrt Real.pi_pos.le
  have hs : 0 < √r := Real.sqrt_pos.mpr hr
  have hT : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
  generalize √π = T at hπ hT
  rw [← hπ]
  field_simp

lemma lead_real_BiPos' {r : ℝ} (hr : 0 < r) :
    2 * (-(1 / (2 * π) * √(π / r) * r * Real.exp (2 / 3 * r ^ 3) *
        Real.cos (5 * π / 6 + π / 6))) = √r * Real.exp (2 / 3 * r ^ 3) / √π := by
  rw [show 5 * π / 6 + π / 6 = π by ring, Real.cos_pi, Real.sqrt_div Real.pi_pos.le]
  have hπ : √π * √π = π := Real.mul_self_sqrt Real.pi_pos.le
  have hs : 0 < √r := Real.sqrt_pos.mpr hr
  have hsr : √r * √r = r := Real.mul_self_sqrt hr.le
  have hT : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
  generalize √π = T at hπ hT
  rw [← hπ]
  generalize √r = u at hsr hs ⊢
  rw [← hsr]
  field_simp

/-- **`Bi` on the positive axis**, in the variable `r = √x`: for `r > 0`,
`|Bi(r²) - e^{(2/3)r³}/(√π √r)| ≤ (4/5) e^{(2/3)r³}/(√r r³)`. -/
theorem airyBi_pos_sq_asymptotic {r : ℝ} (hr : 0 < r) :
    |airyBi (r ^ 2) - Real.exp (2 / 3 * r ^ 3) / (√π * √r)| ≤
      4 / 5 * Real.exp (2 / 3 * r ^ 3) / (√r * r ^ 3) := by
  set A := airyAiC (biW r ^ 2) with hA
  set L : ℂ := ((1 / (2 * π) * √(π / r) * Real.exp (2 / 3 * r ^ 3) : ℝ) : ℂ) *
    cexp (((-(π / 6) : ℝ) : ℂ) * I) with hL
  have h1 := abs_two_re_sub_le norm_airyEps A L
  have h2 : (airyEps * L).re =
      1 / (2 * π) * √(π / r) * Real.exp (2 / 3 * r ^ 3) * Real.cos (π / 6 + (-(π / 6))) := by
    rw [hL, airyEps_eq_exp']; exact re_exp_mul_exp _ _ _
  have h3 : airyBi (r ^ 2) - Real.exp (2 / 3 * r ^ 3) / (√π * √r) =
      (((starRingEnd ℂ) airyEps * (starRingEnd ℂ) A + airyEps * A).re - 2 * (airyEps * L).re) := by
    rw [airyBi_pos_eq, h2, ← lead_real_BiPos hr]
  rw [h3]
  have hw : 0 < (biW r).re := by rw [re_biW]; positivity
  have h4 : ‖A - L‖ ≤ 1 / (2 * π) * Real.exp (2 / 3 * r ^ 3) *
      (5 / 48 * (√(π / (r / 2)) / (r / 2) ^ 3)) := by
    have := norm_airyAiC_sq_sub_le hw
    rw [lead_biAi hr, norm_exp_biW_cube, re_biW] at this
    exact this
  have hE := Real.exp_pos (2 / 3 * r ^ 3)
  have hs : 0 < √r := Real.sqrt_pos.mpr hr
  have h5 := biPos_err0 hr
  calc _ ≤ 2 * ‖A - L‖ := h1
    _ ≤ 2 * (1 / (2 * π) * Real.exp (2 / 3 * r ^ 3) * (5 / 48 * (√(π / (r / 2)) / (r / 2) ^ 3))) := by
        gcongr
    _ = 2 * Real.exp (2 / 3 * r ^ 3) * (1 / (2 * π) * (5 / 48 * (√(π / (r / 2)) / (r / 2) ^ 3))) := by
        ring
    _ ≤ 2 * Real.exp (2 / 3 * r ^ 3) * (2 / 5 * (1 / (√r * r ^ 3))) := by gcongr
    _ = 4 / 5 * Real.exp (2 / 3 * r ^ 3) / (√r * r ^ 3) := by ring

/-- **`Bi'` on the positive axis**, in the variable `r = √x`: for `r > 0`,
`|Bi'(r²) - √r e^{(2/3)r³}/√π| ≤ (7/4) e^{(2/3)r³}/(√r r²)`. -/
theorem airyBiDeriv_pos_sq_asymptotic {r : ℝ} (hr : 0 < r) :
    |airyBiDeriv (r ^ 2) - √r * Real.exp (2 / 3 * r ^ 3) / √π| ≤
      7 / 4 * Real.exp (2 / 3 * r ^ 3) / (√r * r ^ 2) := by
  set A := deriv airyAiC (biW r ^ 2) with hA
  set L : ℂ := -(((1 / (2 * π) * √(π / r) * r * Real.exp (2 / 3 * r ^ 3) : ℝ) : ℂ) *
    cexp (((π / 6 : ℝ) : ℂ) * I)) with hL
  have h1 := abs_two_re_sub_le norm_airyEps_mul_airyOmega A L
  have h2 : ((airyEps * airyOmega) * L).re =
      -(1 / (2 * π) * √(π / r) * r * Real.exp (2 / 3 * r ^ 3) * Real.cos (5 * π / 6 + π / 6)) := by
    rw [hL, mul_neg, Complex.neg_re, airyEps_mul_airyOmega_eq]
    rw [re_exp_mul_exp]
  have h3 : airyBiDeriv (r ^ 2) - √r * Real.exp (2 / 3 * r ^ 3) / √π =
      (((starRingEnd ℂ) (airyEps * airyOmega) * (starRingEnd ℂ) A + (airyEps * airyOmega) * A).re -
        2 * ((airyEps * airyOmega) * L).re) := by
    have := lead_real_BiPos' hr
    rw [airyBiDeriv_pos_eq, h2, ← this]
  rw [h3]
  have hw : 0 < (biW r).re := by rw [re_biW]; positivity
  have h4 : ‖A - L‖ ≤ 1 / (2 * π) * Real.exp (2 / 3 * r ^ 3) *
      (r * (5 / 48 * (√(π / (r / 2)) / (r / 2) ^ 3)) + 1 / 4 * (√(π / (r / 2)) / (r / 2) ^ 2)) := by
    have := norm_deriv_airyAiC_sq_add_le hw
    rw [lead_biAi' hr, norm_exp_biW_cube, re_biW, norm_biW r hr] at this
    rw [hL, sub_neg_eq_add]
    exact this
  have hE := Real.exp_pos (2 / 3 * r ^ 3)
  have hs : 0 < √r := Real.sqrt_pos.mpr hr
  have h5 := biPos_err1 hr
  calc _ ≤ 2 * ‖A - L‖ := h1
    _ ≤ 2 * (1 / (2 * π) * Real.exp (2 / 3 * r ^ 3) *
        (r * (5 / 48 * (√(π / (r / 2)) / (r / 2) ^ 3)) + 1 / 4 * (√(π / (r / 2)) / (r / 2) ^ 2))) := by
        gcongr
    _ = 2 * Real.exp (2 / 3 * r ^ 3) * (1 / (2 * π) *
        (r * (5 / 48 * (√(π / (r / 2)) / (r / 2) ^ 3)) + 1 / 4 * (√(π / (r / 2)) / (r / 2) ^ 2))) := by
        ring
    _ ≤ 2 * Real.exp (2 / 3 * r ^ 3) * (7 / 8 * (1 / (√r * r ^ 2))) := by gcongr
    _ = 7 / 4 * Real.exp (2 / 3 * r ^ 3) / (√r * r ^ 2) := by ring


/-- **DLMF 9.7.7 with explicit remainder**: for every `x > 0`,
`|Bi(x) - π^{-1/2} x^{-1/4} e^{(2/3)x^{3/2}}| ≤ (4/5) x^{-7/4} e^{(2/3)x^{3/2}}`. -/
theorem airyBi_pos_asymptotic {x : ℝ} (hx : 0 < x) :
    |airyBi x - 1 / √π * x ^ (-(1 / 4) : ℝ) * Real.exp (2 / 3 * x ^ (3 / 2 : ℝ))| ≤
      4 / 5 * x ^ (-(7 / 4) : ℝ) * Real.exp (2 / 3 * x ^ (3 / 2 : ℝ)) := by
  have hr : 0 < √x := Real.sqrt_pos.mpr hx
  have h := airyBi_pos_sq_asymptotic hr
  rw [Real.sq_sqrt hx.le] at h
  have hs : 0 < √(√x) := Real.sqrt_pos.mpr hr
  have hT : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
  rw [← sqrt_cube_eq_rpow hx, rpow_neg_quarter hx, rpow_neg_seven_quarter hx]
  convert h using 2
  · field_simp
  · field_simp

/-- **DLMF 9.7.8 with explicit remainder**: for every `x > 0`,
`|Bi'(x) - π^{-1/2} x^{1/4} e^{(2/3)x^{3/2}}| ≤ (7/4) x^{-5/4} e^{(2/3)x^{3/2}}`. -/
theorem airyBiDeriv_pos_asymptotic {x : ℝ} (hx : 0 < x) :
    |airyBiDeriv x - 1 / √π * x ^ (1 / 4 : ℝ) * Real.exp (2 / 3 * x ^ (3 / 2 : ℝ))| ≤
      7 / 4 * x ^ (-(5 / 4) : ℝ) * Real.exp (2 / 3 * x ^ (3 / 2 : ℝ)) := by
  have hr : 0 < √x := Real.sqrt_pos.mpr hx
  have h := airyBiDeriv_pos_sq_asymptotic hr
  rw [Real.sq_sqrt hx.le] at h
  have hs : 0 < √(√x) := Real.sqrt_pos.mpr hr
  have hT : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
  rw [← sqrt_cube_eq_rpow hx, ← sqrt_sqrt_eq_rpow hx, rpow_neg_five_quarter hx, Real.sq_sqrt hx.le]
  convert h using 2
  · field_simp
  · field_simp

/-- info: 'FormalResearch.Special.airyBi_pos_asymptotic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyBi_pos_asymptotic

/-- info: 'FormalResearch.Special.airyBiDeriv_pos_asymptotic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyBiDeriv_pos_asymptotic

end FormalResearch.Special
