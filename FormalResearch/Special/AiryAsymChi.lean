module

public import FormalResearch.Special.AiryAsymChiAux
public import FormalResearch.Special.AiryAsymReal
public import FormalResearch.Special.AiryAsymBiNeg

/-!
# `χ = Ai + iBi` on the negative axis: the `u₁ = 5/72` term of DLMF 9.7.9–9.7.11 with explicit remainder

The saddle-point formula of `AiryAsymSaddle` is expanded one order further: with the fourth-order Taylor remainder of
the cubic phase (`norm_saddlePhase_sub_poly_le`, from `AiryAsymChiAux`),
`e^{-is³/3} = 1 - i s³/3 - s⁶/18 + i s⁹/162 + D(s)`, `|D(s)| ≤ s^{12}/1944`; the odd terms integrate to `0`, the Gaussian
moment `∫ s⁶ e^{-w s²} = (15/(8w³)) (π/w)^{1/2}` is exact for complex `w` (`integral_sixth_gauss_complex`) and
`∫ s^{12} e^{-ρ s²} = (10395/64) √(π/ρ)/ρ⁶`, so for every `w` with `ρ = Re w > 0`

* `norm_airyAiC_sq_third_le`:
  `‖Ai(w²) - (e^{-(2/3)w³}/2π) (π/w)^{1/2} (1 - 5/(48 w³))‖ ≤ (1/2π) ‖e^{-(2/3)w³}‖ (385/4608) √(π/ρ)/ρ⁶`.

At `w = r e^{iπ/6}` (`r = √y`, `w² = -ω² y`, `w³ = i r³`, `ρ ≥ (5/6) r`) and with the rotation identity
`Ai(z) + i Bi(z) = (1 + √3 i) Ai(ω² z) = 2 e^{iπ/3} Ai(ω² z)` (`airyAiC_add_I_mul_airyBiC`, DLMF 9.2.11; a *single*
saddle) this gives, for every `y > 0`, with `ξ = (2/3) y^{3/2}` and `θ = ξ - π/4`:

* `airyChi_neg_asymptotic`
  `‖Ai(-y) + i Bi(-y) - π^{-1/2} y^{-1/4} e^{-iθ} (1 + i (5/72)/ξ)‖ ≤ (1/5) y^{-13/4}`,
  i.e. `χ(-y) = π^{-1/2} y^{-1/4} e^{-iθ} (1 + i u₁ ξ^{-1} + O(ξ^{-2}))`, `u₁ = 5/72`, the relative error being `O(y^{-3})`
  (the order of `u₂`);
* `airyAi_neg_asymptotic_u1`: `|Ai(-y) - π^{-1/2} y^{-1/4} (cos θ + (u₁/ξ) sin θ)| ≤ (1/5) y^{-13/4}` (DLMF 9.7.9 to
  `u₁`), `airyBi_neg_asymptotic_u1`: `|Bi(-y) - π^{-1/2} y^{-1/4} ((u₁/ξ) cos θ - sin θ)| ≤ (1/5) y^{-13/4}` (9.7.11);
* first terms of `χ` and `χ'` (cheap corollaries of the first-order theorems): `airyChi_neg_asymptotic_first`
  (`‖χ(-y) - π^{-1/2} y^{-1/4} e^{-iθ}‖ ≤ y^{-7/4}/4`) and `airyChi'_neg_asymptotic_first`
  (`‖χ'(-y) - i π^{-1/2} y^{1/4} e^{-iθ}‖ ≤ (4/5) y^{-5/4}`).

Numerical check (mpmath, 30 digits, `y ∈ [10^{-1}, 10^{5}]`): `|χ(-y) - main| y^{13/4} ≤ 0.0472` (the limit is
`u₂ · (3/2)² · π^{-1/2} = 0.0472` with `u₂ = 385/10368`); the constant `1/5` is that of the proof.

Not formalised: the next coefficients `u₂, u₃, ...` (the same method needs further Gaussian moments and Taylor
orders), the derivative `χ'` to order `u₁` (the analogue with `Ai'`, `v₁ = -7/72`), and statements for `|arg|` beyond the
negative axis.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.Special

lemma integral_twelfth_gauss {c : ℝ} (hc : 0 < c) :
    ∫ s : ℝ, s ^ 12 * Real.exp (-c * s ^ 2) = 10395 / 64 * √(π / c) / c ^ 6 := by
  have h := integral_comp_abs (f := fun y : ℝ => y ^ 12 * Real.exp (-c * y ^ 2))
  simp only [sq_abs] at h
  have h12 : ∀ s : ℝ, |s| ^ 12 = s ^ 12 := fun s => by
    rw [show (12 : ℕ) = 2 * 6 from rfl, pow_mul, pow_mul, sq_abs]
  simp only [h12] at h
  rw [h]
  have := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 12) (b := c) two_pos (by norm_num) hc
  simp only [Real.rpow_two, show (12 : ℝ) = ((12 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast] at this
  rw [this]
  have hG : Real.Gamma (13 / 2) = 10395 / 64 * √π := by
    have := Real.Gamma_nat_add_half 6
    norm_num [Nat.doubleFactorial] at this
    rw [this]
    ring
  have hE : c ^ (-(((12 : ℕ) : ℝ) + 1) / 2) = (c ^ (1 / 2 : ℝ))⁻¹ / c ^ 6 := by
    rw [show -(((12 : ℕ) : ℝ) + 1) / 2 = -(6 + 1 / 2 : ℝ) by norm_num, Real.rpow_neg hc.le,
      Real.rpow_add hc, show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    field_simp
  have hS : √(π / c) = √π / c ^ (1 / 2 : ℝ) := by
    rw [Real.sqrt_div Real.pi_pos.le, Real.sqrt_eq_rpow c]
  rw [show (((12 : ℕ) : ℝ) + 1) / 2 = 13 / 2 by norm_num, hG, hE, hS]
  field_simp


/-- The fourth-order Taylor remainder of the cubic phase: for every `s`,
`‖e^{-is³/3} - (1 - i s³/3 - s⁶/18 + i s⁹/162)‖ ≤ s^{12}/1944`. -/
lemma norm_saddlePhase_sub_poly_le (s : ℝ) :
    ‖saddlePhase s - (1 - I * (s : ℂ) ^ 3 / 3 - (s : ℂ) ^ 6 / 18 + I * (s : ℂ) ^ 9 / 162)‖ ≤
      s ^ 12 / 1944 := by
  have h := norm_exp_I_mul_sub_cubic_le (-(s ^ 3 / 3))
  have e : saddlePhase s - (1 - I * (s : ℂ) ^ 3 / 3 - (s : ℂ) ^ 6 / 18 + I * (s : ℂ) ^ 9 / 162) =
      cexp (I * ((-(s ^ 3 / 3) : ℝ) : ℂ)) - 1 - I * ((-(s ^ 3 / 3) : ℝ) : ℂ) -
        (I * ((-(s ^ 3 / 3) : ℝ) : ℂ)) ^ 2 / 2 - (I * ((-(s ^ 3 / 3) : ℝ) : ℂ)) ^ 3 / 6 := by
    unfold saddlePhase
    push_cast
    have hI : I ^ 3 = -I := by rw [pow_succ, Complex.I_sq]; ring
    linear_combination ((s : ℂ) ^ 6 / 18) * Complex.I_sq + (-(s : ℂ) ^ 9 / 162) * hI
  rw [e]
  refine h.trans (le_of_eq ?_)
  ring


/-- **Third-order Gaussian estimate** for `J₀(w) = ∫ exp(-w s² - i s³/3) ds`, `ρ = Re w > 0`:
`‖J₀ - (π/w)^{1/2} (1 - 5/(48 w³))‖ ≤ (385/4608) √(π/ρ)/ρ⁶`. -/
theorem norm_saddleJ0_third_le {w : ℂ} (hw : 0 < w.re) :
    ‖saddleJ0 w - (π / w) ^ (1 / 2 : ℂ) * (1 - 5 / (48 * w ^ 3))‖ ≤
      385 / 4608 * (√(π / w.re) / w.re ^ 6) := by
  have hw0 : w ≠ 0 := fun h => by simp [h] at hw
  set D : ℝ → ℂ := fun s => saddlePhase s -
    (1 - I * (s : ℂ) ^ 3 / 3 - (s : ℂ) ^ 6 / 18 + I * (s : ℂ) ^ 9 / 162) with hD
  have hDb : ∀ s, ‖D s‖ ≤ 1 / 1944 * s ^ 12 := fun s => by
    have := norm_saddlePhase_sub_poly_le s
    simpa [hD, div_eq_inv_mul] using this
  have hDc : Continuous D := by simp only [hD, saddlePhase]; fun_prop
  have iG := integrable_pow_cexp_gauss hw 0
  have i3 := integrable_pow_cexp_gauss hw 3
  have i6 := integrable_pow_cexp_gauss hw 6
  have i9 := integrable_pow_cexp_gauss hw 9
  simp only [pow_zero, one_mul] at iG
  have iDG : Integrable (fun s : ℝ => D s * saddleGauss w s) :=
    integrable_gauss_mul_of_le hw hDc 12 (1 / 1944) (fun s => by
      have h12 : |s| ^ 12 = s ^ 12 := by
        rw [show (12 : ℕ) = 2 * 6 from rfl, pow_mul, pow_mul, sq_abs]
      rw [h12]; exact hDb s)
  have hsplit : ∀ s : ℝ, saddlePhase s * saddleGauss w s =
      cexp (-w * (s : ℂ) ^ 2) - I / 3 * ((s : ℂ) ^ 3 * cexp (-w * (s : ℂ) ^ 2)) -
        1 / 18 * ((s : ℂ) ^ 6 * cexp (-w * (s : ℂ) ^ 2)) +
        I / 162 * ((s : ℂ) ^ 9 * cexp (-w * (s : ℂ) ^ 2)) + D s * saddleGauss w s := by
    intro s; simp only [hD, saddleGauss]; ring
  have hodd3 : ∫ s : ℝ, (s : ℂ) ^ 3 * cexp (-w * (s : ℂ) ^ 2) = 0 := by
    refine integral_eq_zero_of_odd fun s => ?_
    push_cast; ring_nf
  have hodd9 : ∫ s : ℝ, (s : ℂ) ^ 9 * cexp (-w * (s : ℂ) ^ 2) = 0 := by
    refine integral_eq_zero_of_odd fun s => ?_
    push_cast; ring_nf
  have hJ : saddleJ0 w - (π / w) ^ (1 / 2 : ℂ) * (1 - 5 / (48 * w ^ 3)) =
      ∫ s : ℝ, D s * saddleGauss w s := by
    unfold saddleJ0
    simp_rw [hsplit]
    have iA : Integrable (fun s : ℝ => cexp (-w * (s : ℂ) ^ 2) -
        I / 3 * ((s : ℂ) ^ 3 * cexp (-w * (s : ℂ) ^ 2))) := iG.sub (i3.const_mul (I / 3))
    have iB : Integrable (fun s : ℝ => cexp (-w * (s : ℂ) ^ 2) -
        I / 3 * ((s : ℂ) ^ 3 * cexp (-w * (s : ℂ) ^ 2)) -
        1 / 18 * ((s : ℂ) ^ 6 * cexp (-w * (s : ℂ) ^ 2))) := iA.sub (i6.const_mul (1 / 18))
    have iC : Integrable (fun s : ℝ => cexp (-w * (s : ℂ) ^ 2) -
        I / 3 * ((s : ℂ) ^ 3 * cexp (-w * (s : ℂ) ^ 2)) -
        1 / 18 * ((s : ℂ) ^ 6 * cexp (-w * (s : ℂ) ^ 2)) +
        I / 162 * ((s : ℂ) ^ 9 * cexp (-w * (s : ℂ) ^ 2))) := iB.add (i9.const_mul (I / 162))
    rw [integral_add iC iDG, integral_add iB (i9.const_mul (I / 162)), integral_sub iA (i6.const_mul (1 / 18)),
      integral_sub iG (i3.const_mul (I / 3)), integral_const_mul, integral_const_mul,
      integral_const_mul, hodd3, hodd9, integral_sixth_gauss_complex hw, integral_gaussian_complex hw]
    field_simp
    ring
  rw [hJ]
  have i12 : Integrable (fun s : ℝ => 1 / 1944 * (s ^ 12 * Real.exp (-w.re * s ^ 2))) := by
    have := (integrable_abs_pow_gauss hw 12).const_mul (1 / 1944)
    simpa [show ∀ s : ℝ, |s| ^ 12 = s ^ 12 from fun s => by
      rw [show (12 : ℕ) = 2 * 6 from rfl, pow_mul, pow_mul, sq_abs]] using this
  refine (norm_integral_le_of_norm_le i12 (Filter.Eventually.of_forall fun s => ?_)).trans ?_
  · rw [norm_mul, norm_saddleGauss]
    have := mul_le_mul_of_nonneg_right (hDb s) (Real.exp_pos (-w.re * s ^ 2)).le
    simpa [mul_assoc] using this
  · rw [integral_const_mul, integral_twelfth_gauss hw]
    apply le_of_eq
    ring


/-- **Third-order saddle estimate for `Ai(w²)`**, `Re w > 0`:
`‖Ai(w²) - (e^{-(2/3)w³}/2π) (π/w)^{1/2} (1 - 5/(48 w³))‖ ≤ (1/2π) ‖e^{-(2/3)w³}‖ (385/4608) √(π/ρ)/ρ⁶`. -/
theorem norm_airyAiC_sq_third_le {w : ℂ} (hw : 0 < w.re) :
    ‖airyAiC (w ^ 2) - (1 / (2 * (π : ℂ))) * cexp (-(2 / 3) * w ^ 3) *
        ((π / w) ^ (1 / 2 : ℂ) * (1 - 5 / (48 * w ^ 3)))‖ ≤
      1 / (2 * π) * ‖cexp (-(2 / 3) * w ^ 3)‖ * (385 / 4608 * (√(π / w.re) / w.re ^ 6)) := by
  have e : airyAiC (w ^ 2) - (1 / (2 * (π : ℂ))) * cexp (-(2 / 3) * w ^ 3) *
        ((π / w) ^ (1 / 2 : ℂ) * (1 - 5 / (48 * w ^ 3))) =
      (1 / (2 * (π : ℂ))) * cexp (-(2 / 3) * w ^ 3) *
        (saddleJ0 w - (π / w) ^ (1 / 2 : ℂ) * (1 - 5 / (48 * w ^ 3))) := by
    rw [airyAiC_sq_eq hw]; ring
  rw [e, norm_mul, norm_mul]
  have h1 : ‖(1 / (2 * (π : ℂ)))‖ = 1 / (2 * π) := by
    rw [norm_div, norm_one, norm_mul]; simp [abs_of_pos Real.pi_pos]
  rw [h1]
  exact mul_le_mul_of_nonneg_left (norm_saddleJ0_third_le hw) (by positivity)

/-- `Ai(z) + i Bi(z) = (1 + √3 i) Ai(ω² z) = 2 e^{iπ/3} Ai(ω² z)` (DLMF 9.2.11). -/
theorem airyAiC_add_I_mul_airyBiC (z : ℂ) :
    airyAiC z + I * airyBiC z = (1 + (√3 : ℝ) * I) * airyAiC (airyOmega ^ 2 * z) := by
  have h := airyAiC_rotation z
  have h1 : -airyOmega + I * airyEps = 0 := by
    exact Complex.ext (by simp [airyEps, airyOmega]; norm_num) (by simp [airyEps, airyOmega])
  have h2 : -(airyOmega ^ 2) + I * (starRingEnd ℂ) airyEps = 1 + (√3 : ℝ) * I := by
    rw [airyOmega_sq_eq]
    exact Complex.ext (by simp [airyEps]; norm_num) (by simp [airyEps])
  unfold airyBiC
  linear_combination h + (airyAiC (airyOmega * z)) * h1 + (airyAiC (airyOmega ^ 2 * z)) * h2


lemma one_add_sqrt3_I : (1 + (√3 : ℝ) * I) = 2 * cexp (((π / 3 : ℝ) : ℂ) * I) := by
  have hre : (cexp (((π / 3 : ℝ) : ℂ) * I)).re = 1 / 2 := by
    rw [Complex.exp_ofReal_mul_I_re, Real.cos_pi_div_three]
  have him : (cexp (((π / 3 : ℝ) : ℂ) * I)).im = √3 / 2 := by
    rw [Complex.exp_ofReal_mul_I_im, Real.sin_pi_div_three]
  generalize cexp (((π / 3 : ℝ) : ℂ) * I) = E at hre him ⊢
  apply Complex.ext
  · simp [hre]
  · simp [him]; ring

/-- The leading terms of `2 e^{iπ/3} Ai(w²)` at `w = r e^{iπ/6}`, with the `u₁` correction. -/
lemma chi_lead {r : ℝ} (hr : 0 < r) :
    (1 + (√3 : ℝ) * I) * ((1 / (2 * (π : ℂ))) * cexp (-(2 / 3) * negW r ^ 3) *
        ((π / negW r) ^ (1 / 2 : ℂ) * (1 - 5 / (48 * negW r ^ 3)))) =
      ((1 / (√π * √r) : ℝ) : ℂ) * cexp (((-(2 / 3 * r ^ 3 - π / 4) : ℝ) : ℂ) * I) *
        (1 + ((5 / (48 * r ^ 3) : ℝ) : ℂ) * I) := by
  rw [exp_negW_cube, sqrt_pi_div_negW hr, negW_cube, one_add_sqrt3_I]
  have hE : cexp (((π / 3 : ℝ) : ℂ) * I) * cexp (((-(2 / 3 * r ^ 3) : ℝ) : ℂ) * I) *
      cexp (((-(π / 12) : ℝ) : ℂ) * I) = cexp (((-(2 / 3 * r ^ 3 - π / 4) : ℝ) : ℂ) * I) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; push_cast; ring
  rw [← hE]
  generalize cexp (((π / 3 : ℝ) : ℂ) * I) = E1
  generalize cexp (((-(2 / 3 * r ^ 3) : ℝ) : ℂ) * I) = E2
  generalize cexp (((-(π / 12) : ℝ) : ℂ) * I) = E3
  have hπ : √π * √π = π := Real.mul_self_sqrt Real.pi_pos.le
  have hs : 0 < √r := Real.sqrt_pos.mpr hr
  have hT : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
  rw [Real.sqrt_div Real.pi_pos.le]
  have hπ' : (π : ℂ) = (√π : ℂ) * (√π : ℂ) := by exact_mod_cast hπ.symm
  have hT' : (√π : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  have hs' : (√r : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  push_cast
  rw [hπ']
  field_simp
  ring_nf
  simp [Complex.I_sq]
  ring


lemma errChi_le {r ρ : ℝ} (hr : 0 < r) (hρ : 5 / 6 * r ≤ ρ) :
    2 * (1 / (2 * π) * (385 / 4608 * (√(π / ρ) / ρ ^ 6))) ≤ 1 / 5 * (1 / (√r * r ^ 6)) := by
  have h6 := sqrt_div_pow_le hr hρ 6
  have hs : 0 < √r := Real.sqrt_pos.mpr hr
  have hm : 0 < √r * r ^ 6 := by positivity
  have hT := sqrtpi_ge
  have hπ : √π * √π = π := Real.mul_self_sqrt Real.pi_pos.le
  have hT0 : 0 < √π := by linarith
  calc 2 * (1 / (2 * π) * (385 / 4608 * (√(π / ρ) / ρ ^ 6)))
      ≤ 2 * (1 / (2 * π) * (385 / 4608 * (10 / 9 * (6 / 5) ^ 6 * √π / (√r * r ^ 6)))) := by gcongr
    _ = (385 / 4608 * (10 / 9) * (6 / 5) ^ 6 / √π) * (1 / (√r * r ^ 6)) := by
        generalize √π = T at hπ hT0
        rw [← hπ]
        field_simp
    _ ≤ 1 / 5 * (1 / (√r * r ^ 6)) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        rw [div_le_iff₀ hT0]
        nlinarith

lemma norm_one_add_sqrt3_I : ‖(1 + (√3 : ℝ) * I)‖ = 2 := by
  rw [one_add_sqrt3_I, norm_mul, Complex.norm_exp_ofReal_mul_I]
  simp

/-- **`χ = Ai + iBi` on the negative axis with the `u₁ = 5/72` correction**, in the variable `r = √y`:
for `r > 0`, with `φ = (2/3) r³ - π/4`,
`‖Ai(-r²) + i Bi(-r²) - (1/(√π √r)) e^{-iφ} (1 + 5i/(48 r³))‖ ≤ (1/5)/(√r r⁶)`. -/
theorem airyChi_neg_sq_asymptotic {r : ℝ} (hr : 0 < r) :
    ‖((airyAi (-(r ^ 2)) : ℝ) : ℂ) + I * ((airyBi (-(r ^ 2)) : ℝ) : ℂ) -
        ((1 / (√π * √r) : ℝ) : ℂ) * cexp (((-(2 / 3 * r ^ 3 - π / 4) : ℝ) : ℂ) * I) *
          (1 + ((5 / (48 * r ^ 3) : ℝ) : ℂ) * I)‖ ≤ 1 / 5 * (1 / (√r * r ^ 6)) := by
  have hw : 0 < (negW r).re := by rw [re_negW]; positivity
  have h := norm_airyAiC_sq_third_le hw
  rw [norm_exp_negW_cube, mul_one, re_negW r] at h
  have hχ : ((airyAi (-(r ^ 2)) : ℝ) : ℂ) + I * ((airyBi (-(r ^ 2)) : ℝ) : ℂ) =
      (1 + (√3 : ℝ) * I) * airyAiC (negW r ^ 2) := by
    have := airyAiC_add_I_mul_airyBiC ((-(r ^ 2) : ℝ) : ℂ)
    rw [airyAiC_ofReal, airyBiC_ofReal, ← negW_sq] at this
    exact this
  rw [hχ, ← chi_lead hr, ← mul_sub, norm_mul, norm_one_add_sqrt3_I]
  have h5 := errChi_le hr (five_six_le_re_negW r hr)
  have h' : ‖airyAiC (negW r ^ 2) - (1 / (2 * (π : ℂ))) * cexp (-(2 / 3) * negW r ^ 3) *
      ((π / negW r) ^ (1 / 2 : ℂ) * (1 - 5 / (48 * negW r ^ 3)))‖ ≤
      1 / (2 * π) * (385 / 4608 * (√(π / (negW r).re) / (negW r).re ^ 6)) := by
    simpa [re_negW] using h
  calc 2 * ‖_‖ ≤ 2 * (1 / (2 * π) * (385 / 4608 * (√(π / (negW r).re) / (negW r).re ^ 6))) := by
        gcongr
    _ ≤ _ := h5


lemma re_chi_lead (c t φ : ℝ) :
    ((c : ℂ) * cexp (((-φ : ℝ) : ℂ) * I) * (1 + (t : ℂ) * I)).re = c * (Real.cos φ + t * Real.sin φ) := by
  have h1 := Complex.exp_ofReal_mul_I_re (-φ)
  have h2 := Complex.exp_ofReal_mul_I_im (-φ)
  rw [Real.cos_neg] at h1
  rw [Real.sin_neg] at h2
  generalize cexp (((-φ : ℝ) : ℂ) * I) = E at h1 h2
  simp [Complex.mul_re, Complex.mul_im, h1, h2]
  ring

lemma im_chi_lead (c t φ : ℝ) :
    ((c : ℂ) * cexp (((-φ : ℝ) : ℂ) * I) * (1 + (t : ℂ) * I)).im = c * (t * Real.cos φ - Real.sin φ) := by
  have h1 := Complex.exp_ofReal_mul_I_re (-φ)
  have h2 := Complex.exp_ofReal_mul_I_im (-φ)
  rw [Real.cos_neg] at h1
  rw [Real.sin_neg] at h2
  generalize cexp (((-φ : ℝ) : ℂ) * I) = E at h1 h2
  simp [Complex.mul_re, Complex.mul_im, h1, h2]
  ring

/-- **DLMF 9.7.9 with the `u₁ = 5/72` term**, in `r = √y`: with `φ = (2/3) r³ - π/4`,
`|Ai(-r²) - (1/(√π √r)) (cos φ + (5/(48 r³)) sin φ)| ≤ (1/5)/(√r r⁶)`. -/
theorem airyAi_neg_sq_asymptotic_u1 {r : ℝ} (hr : 0 < r) :
    |airyAi (-(r ^ 2)) - 1 / (√π * √r) * (Real.cos (2 / 3 * r ^ 3 - π / 4) +
        5 / (48 * r ^ 3) * Real.sin (2 / 3 * r ^ 3 - π / 4))| ≤ 1 / 5 * (1 / (√r * r ^ 6)) := by
  have h := airyChi_neg_sq_asymptotic hr
  refine (le_trans ?_ h)
  refine le_trans (le_of_eq ?_) (Complex.abs_re_le_norm _)
  rw [Complex.sub_re, re_chi_lead]
  simp

/-- **DLMF 9.7.11 with the `u₁ = 5/72` term**, in `r = √y`:
`|Bi(-r²) - (1/(√π √r)) ((5/(48 r³)) cos φ - sin φ)| ≤ (1/5)/(√r r⁶)`. -/
theorem airyBi_neg_sq_asymptotic_u1 {r : ℝ} (hr : 0 < r) :
    |airyBi (-(r ^ 2)) - 1 / (√π * √r) * (5 / (48 * r ^ 3) * Real.cos (2 / 3 * r ^ 3 - π / 4) -
        Real.sin (2 / 3 * r ^ 3 - π / 4))| ≤ 1 / 5 * (1 / (√r * r ^ 6)) := by
  have h := airyChi_neg_sq_asymptotic hr
  refine (le_trans ?_ h)
  refine le_trans (le_of_eq ?_) (Complex.abs_im_le_norm _)
  rw [Complex.sub_im, im_chi_lead]
  simp


lemma rpow_neg_thirteen_quarter {y : ℝ} (hy : 0 < y) :
    y ^ (-(13 / 4) : ℝ) = 1 / (√(√y) * (√y) ^ 6) := by
  have h6 : (√y) ^ 6 = y ^ 3 := by
    rw [show (6 : ℕ) = 2 * 3 from rfl, pow_mul, Real.sq_sqrt hy.le]
  rw [Real.rpow_neg hy.le, sqrt_sqrt_eq_rpow hy, h6, ← Real.rpow_natCast y 3,
    ← Real.rpow_add hy]
  norm_num

/-- **`χ = Ai + iBi` with the `u₁ = 5/72` correction** (DLMF 9.7.9–9.7.11 combined, 9.7.3 for `u₁`): for every `y > 0`,
with `ξ = (2/3) y^{3/2}` and `θ = ξ - π/4`,
`‖Ai(-y) + i Bi(-y) - π^{-1/2} y^{-1/4} e^{-iθ} (1 + i (5/72)/ξ)‖ ≤ (1/5) y^{-13/4}`,
i.e. relative error `O(y^{-3}) = O(ξ^{-2})` (the order of `u₂`). -/
theorem airyChi_neg_asymptotic {y : ℝ} (hy : 0 < y) :
    ‖((airyAi (-y) : ℝ) : ℂ) + I * ((airyBi (-y) : ℝ) : ℂ) -
        ((1 / √π * y ^ (-(1 / 4) : ℝ) : ℝ) : ℂ) *
          cexp (((-(2 / 3 * y ^ (3 / 2 : ℝ) - π / 4) : ℝ) : ℂ) * I) *
          (1 + (((5 / 72) / (2 / 3 * y ^ (3 / 2 : ℝ)) : ℝ) : ℂ) * I)‖ ≤
      1 / 5 * y ^ (-(13 / 4) : ℝ) := by
  have hr : 0 < √y := Real.sqrt_pos.mpr hy
  have h := airyChi_neg_sq_asymptotic hr
  rw [Real.sq_sqrt hy.le] at h
  have hs : 0 < √(√y) := Real.sqrt_pos.mpr hr
  have hT : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
  have e1 : (1 / √π * y ^ (-(1 / 4) : ℝ) : ℝ) = 1 / (√π * √(√y)) := by
    rw [rpow_neg_quarter hy]; field_simp
  have e2 : ((5 / 72) / (2 / 3 * y ^ (3 / 2 : ℝ)) : ℝ) = 5 / (48 * (√y) ^ 3) := by
    rw [← sqrt_cube_eq_rpow hy]
    field_simp
    ring
  rw [e1, e2, rpow_neg_thirteen_quarter hy, ← sqrt_cube_eq_rpow hy]
  exact h

/-- **DLMF 9.7.9 with the `u₁` term**: `|Ai(-y) - π^{-1/2} y^{-1/4} (cos θ + ((5/72)/ξ) sin θ)| ≤ (1/5) y^{-13/4}`. -/
theorem airyAi_neg_asymptotic_u1 {y : ℝ} (hy : 0 < y) :
    |airyAi (-y) - 1 / √π * y ^ (-(1 / 4) : ℝ) *
        (Real.cos (2 / 3 * y ^ (3 / 2 : ℝ) - π / 4) +
          (5 / 72) / (2 / 3 * y ^ (3 / 2 : ℝ)) * Real.sin (2 / 3 * y ^ (3 / 2 : ℝ) - π / 4))| ≤
      1 / 5 * y ^ (-(13 / 4) : ℝ) := by
  refine le_trans ?_ (airyChi_neg_asymptotic hy)
  refine le_trans (le_of_eq ?_) (Complex.abs_re_le_norm _)
  rw [Complex.sub_re, re_chi_lead]
  simp

/-- **DLMF 9.7.11 with the `u₁` term**: `|Bi(-y) - π^{-1/2} y^{-1/4} (((5/72)/ξ) cos θ - sin θ)| ≤ (1/5) y^{-13/4}`. -/
theorem airyBi_neg_asymptotic_u1 {y : ℝ} (hy : 0 < y) :
    |airyBi (-y) - 1 / √π * y ^ (-(1 / 4) : ℝ) *
        ((5 / 72) / (2 / 3 * y ^ (3 / 2 : ℝ)) * Real.cos (2 / 3 * y ^ (3 / 2 : ℝ) - π / 4) -
          Real.sin (2 / 3 * y ^ (3 / 2 : ℝ) - π / 4))| ≤
      1 / 5 * y ^ (-(13 / 4) : ℝ) := by
  refine le_trans ?_ (airyChi_neg_asymptotic hy)
  refine le_trans (le_of_eq ?_) (Complex.abs_im_le_norm _)
  rw [Complex.sub_im, im_chi_lead]
  simp

lemma norm_add_I_mul_le (a b : ℝ) : ‖(a : ℂ) + I * (b : ℂ)‖ ≤ |a| + |b| := by
  refine (norm_add_le _ _).trans ?_
  simp

lemma mul_exp_neg_I (c φ : ℝ) :
    (c : ℂ) * cexp (((-φ : ℝ) : ℂ) * I) = ((c * Real.cos φ : ℝ) : ℂ) + I * ((-(c * Real.sin φ) : ℝ) : ℂ) := by
  have h1 := Complex.exp_ofReal_mul_I_re (-φ)
  have h2 := Complex.exp_ofReal_mul_I_im (-φ)
  rw [Real.cos_neg] at h1
  rw [Real.sin_neg] at h2
  generalize cexp (((-φ : ℝ) : ℂ) * I) = E at h1 h2
  apply Complex.ext
  · rw [Complex.mul_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, h1]
    ring
  · rw [Complex.mul_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, h2]
    ring

lemma chi_algebra1 (a b c C S : ℝ) :
    (a : ℂ) + I * (b : ℂ) - ((c * C : ℝ) : ℂ) - I * ((-(c * S) : ℝ) : ℂ) =
      ((a - c * C : ℝ) : ℂ) + I * ((b + c * S : ℝ) : ℂ) := by
  push_cast; ring

lemma chi_algebra2 (a b c C S : ℝ) :
    (a : ℂ) + I * (b : ℂ) - I * (((c * C : ℝ) : ℂ) + I * ((-(c * S) : ℝ) : ℂ)) =
      ((a - c * S : ℝ) : ℂ) + I * ((b - c * C : ℝ) : ℂ) := by
  push_cast
  have hI : I * I = -1 := Complex.I_mul_I
  linear_combination ((c : ℂ) * S) * hI

/-- **`χ = Ai + iBi`, first term** (from `airyAi_neg_asymptotic`, `airyBi_neg_asymptotic`): for `y > 0`,
`‖Ai(-y) + i Bi(-y) - π^{-1/2} y^{-1/4} e^{-i(ξ - π/4)}‖ ≤ (1/4) y^{-7/4}`. -/
theorem airyChi_neg_asymptotic_first {y : ℝ} (hy : 0 < y) :
    ‖((airyAi (-y) : ℝ) : ℂ) + I * ((airyBi (-y) : ℝ) : ℂ) -
        ((1 / √π * y ^ (-(1 / 4) : ℝ) : ℝ) : ℂ) *
          cexp (((-(2 / 3 * y ^ (3 / 2 : ℝ) - π / 4) : ℝ) : ℂ) * I)‖ ≤ 1 / 4 * y ^ (-(7 / 4) : ℝ) := by
  have h1 := airyAi_neg_asymptotic hy
  have h2 := airyBi_neg_asymptotic hy
  rw [mul_exp_neg_I]
  have e := chi_algebra1 (airyAi (-y)) (airyBi (-y)) (1 / √π * y ^ (-(1 / 4) : ℝ))
    (Real.cos (2 / 3 * y ^ (3 / 2 : ℝ) - π / 4)) (Real.sin (2 / 3 * y ^ (3 / 2 : ℝ) - π / 4))
  rw [← sub_sub, e]
  refine (norm_add_I_mul_le _ _).trans ?_
  have h2' : |airyBi (-y) + 1 / √π * y ^ (-(1 / 4) : ℝ) * Real.sin (2 / 3 * y ^ (3 / 2 : ℝ) - π / 4)| ≤
      1 / 8 * y ^ (-(7 / 4) : ℝ) := h2
  rw [mul_assoc] at h2'
  linarith

/-- **`χ' = Ai' + iBi'`, first term** (from `airyAi'_neg_asymptotic`, `airyBiDeriv_neg_asymptotic`): for `y > 0`,
`‖Ai'(-y) + i Bi'(-y) - i π^{-1/2} y^{1/4} e^{-i(ξ - π/4)}‖ ≤ (4/5) y^{-5/4}`. -/
theorem airyChi'_neg_asymptotic_first {y : ℝ} (hy : 0 < y) :
    ‖((airyAi' (-y) : ℝ) : ℂ) + I * ((airyBiDeriv (-y) : ℝ) : ℂ) -
        I * (((1 / √π * y ^ (1 / 4 : ℝ) : ℝ) : ℂ) *
          cexp (((-(2 / 3 * y ^ (3 / 2 : ℝ) - π / 4) : ℝ) : ℂ) * I))‖ ≤ 4 / 5 * y ^ (-(5 / 4) : ℝ) := by
  have h1 := airyAi'_neg_asymptotic hy
  have h2 := airyBiDeriv_neg_asymptotic hy
  rw [mul_exp_neg_I]
  have e := chi_algebra2 (airyAi' (-y)) (airyBiDeriv (-y)) (1 / √π * y ^ (1 / 4 : ℝ))
    (Real.cos (2 / 3 * y ^ (3 / 2 : ℝ) - π / 4)) (Real.sin (2 / 3 * y ^ (3 / 2 : ℝ) - π / 4))
  rw [e]
  refine (norm_add_I_mul_le _ _).trans ?_
  linarith

/-- info: 'FormalResearch.Special.norm_saddleJ0_third_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.norm_saddleJ0_third_le

/-- info: 'FormalResearch.Special.norm_airyAiC_sq_third_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.norm_airyAiC_sq_third_le

/-- info: 'FormalResearch.Special.airyAiC_add_I_mul_airyBiC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyAiC_add_I_mul_airyBiC

/-- info: 'FormalResearch.Special.airyChi_neg_asymptotic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyChi_neg_asymptotic

/-- info: 'FormalResearch.Special.airyAi_neg_asymptotic_u1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyAi_neg_asymptotic_u1

/-- info: 'FormalResearch.Special.airyBi_neg_asymptotic_u1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyBi_neg_asymptotic_u1

/-- info: 'FormalResearch.Special.airyChi_neg_asymptotic_first' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyChi_neg_asymptotic_first

/-- info: 'FormalResearch.Special.airyChi'_neg_asymptotic_first' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyChi'_neg_asymptotic_first

end FormalResearch.Special
