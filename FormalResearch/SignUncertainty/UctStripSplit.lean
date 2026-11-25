module

public import FormalResearch.SignUncertainty.UctAiryTransPhi
public import FormalResearch.CohnElkies.MellinAiryToolkit
public import FormalResearch.CohnElkies.AirySeedFloors
public import FormalResearch.CohnElkies.TwoSaddleContraction
public import FormalResearch.CohnElkies.AiryWindowInversion

/-!
# `uct:strip-split` (1) and (3): splitting of the strip kernel, boundary signs and global ratio bounds (F2a)

Source: `CFT/sign_uncertainty/paper/constant_terms_upper.tex`, Lemma `uct:strip-split` (parts (1) and (3)); part (2) is in `UctStripIntegrals`.
Notation: `H_* = uctHstar`, `H_CE = uctHCE`; `m(τ) = ℓ(πτ/2)` with `ℓ = ceEll` (`log(x coth x)`), `m' = uctMderiv`; `τ₀ = tau0 = m⁻¹`;
the envelopes `I_fl, I_osc^*, I_osc^CE, I_osc^ĥ, I_fl^ĥ` of `(uct:envelopes)` are `uctIfl, uctIoscStar, uctIoscCE, uctIoscH, uctIflH`
(with the coefficients `(uct:coeffs)`, `uctAlphaFl`, `uctAlphaOsc = |C_Ai| √(π/3)`, `uctAlphaH = π^{3/2}|C_Ai|/4`, `uctAlphaOsc_eq`, `uctAlphaH_eq`).

* `uct_H_split` : `(uct:H-split)` on `ℂ ∖ ℤ`.  `uct_HCE_signs` : the boundary signs and `|H_CE(1-σ-iτ)| ≤ H_CE(1-σ)`.
* `uct_strip_split_ratios` : `(uct:global-ratios)` `r_CE(τ) < 1`, `r_ĥ(τ;1) < 1` for every `τ > 0`, and `1 - r_CE(τ₀(L)) ≥ c_r min(L,1)` with `c_r = 1/6`.
  The inputs are the comparison inequalities of `mat:T4(a)` (`ceEll_lt`, `ceEll_deriv_gt`, already formalised) and `sinh x ≥ x(1+x²/6)`,
  `sinh(2x) ≥ 2x(1 + 2t + 6t²/5)`; the quantitative `c_r` follows from the same chain without the Taylor expansion of `r_CE` at `0` (`1 - r_CE ≥ (1 - 1/(1+t/2))/2`).
  The expansions `r_CE = 1 - (13π²/240) τ² + O(τ⁴)` and `r_ĥ = 1 - (19π²/240) τ² + O(τ⁴)` are not formalised here.

Class: proved, no hypotheses.  Axiom guards are at the end.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.Special

/-- `H_*(ζ) = π² cos(πζ) / sin²(πζ)`. -/
noncomputable def uctHstar (ζ : ℂ) : ℂ := (π : ℂ) ^ 2 * Complex.cos (π * ζ) / Complex.sin (π * ζ) ^ 2

/-- `H_CE(ζ) = π² / (4 sin²(πζ/2))`. -/
noncomputable def uctHCE (ζ : ℂ) : ℂ := (π : ℂ) ^ 2 / (4 * Complex.sin (π * ζ / 2) ^ 2)

lemma sin_pi_ne_zero {ζ : ℂ} (hζ : ∀ n : ℤ, ζ ≠ n) : Complex.sin (π * ζ) ≠ 0 := by
  intro h
  obtain ⟨n, hn⟩ := Complex.sin_eq_zero_iff.mp h
  apply hζ n
  have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  apply mul_left_cancel₀ hpi
  rw [hn]; ring

/-- `(uct:H-split)`: `H_*(ζ) = H_CE(ζ) - H_CE(1 - ζ)` on `ℂ ∖ ℤ`. -/
theorem uct_H_split {ζ : ℂ} (hζ : ∀ n : ℤ, ζ ≠ n) : uctHstar ζ = uctHCE ζ - uctHCE (1 - ζ) := by
  have hs2 := sin_pi_ne_zero hζ
  have e1 : Complex.sin (π * ζ) = 2 * Complex.sin (π * ζ / 2) * Complex.cos (π * ζ / 2) := by
    rw [← Complex.sin_two_mul]; congr 1; ring
  have e2 : Complex.cos (π * ζ) = Complex.cos (π * ζ / 2) ^ 2 - Complex.sin (π * ζ / 2) ^ 2 := by
    rw [← Complex.cos_two_mul']; congr 1; ring
  have e3 : Complex.sin (π * (1 - ζ) / 2) = Complex.cos (π * ζ / 2) := by
    rw [show (π : ℂ) * (1 - ζ) / 2 = π / 2 - π * ζ / 2 by ring, Complex.sin_pi_div_two_sub]
  have hsc : Complex.sin (π * ζ / 2) * Complex.cos (π * ζ / 2) ≠ 0 := by
    intro h; apply hs2; rw [e1]; rw [mul_assoc, h]; ring
  have hs : Complex.sin (π * ζ / 2) ≠ 0 := left_ne_zero_of_mul hsc
  have hc : Complex.cos (π * ζ / 2) ≠ 0 := right_ne_zero_of_mul hsc
  unfold uctHstar uctHCE
  rw [e3, e1, e2]
  field_simp
  ring


lemma uctHCE_imag (τ : ℝ) :
    uctHCE ((τ : ℂ) * Complex.I) = ((-(π ^ 2 / (4 * Real.sinh (π * τ / 2) ^ 2)) : ℝ) : ℂ) := by
  unfold uctHCE
  have h1 : Complex.sin (π * ((τ : ℂ) * Complex.I) / 2) = (Real.sinh (π * τ / 2) : ℂ) * Complex.I := by
    rw [show (π : ℂ) * ((τ : ℂ) * Complex.I) / 2 = ((π * τ / 2 : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.sin_mul_I, ← Complex.ofReal_sinh]
  rw [h1]
  have h : 4 * ((Real.sinh (π * τ / 2) : ℂ) * Complex.I) ^ 2 = -(4 * (Real.sinh (π * τ / 2) : ℂ) ^ 2) := by
    rw [mul_pow, Complex.I_sq]; ring
  rw [h, div_neg]; push_cast; ring

lemma uctHCE_one_add_imag (τ : ℝ) :
    uctHCE (1 + (τ : ℂ) * Complex.I) = ((π ^ 2 / (4 * Real.cosh (π * τ / 2) ^ 2) : ℝ) : ℂ) := by
  unfold uctHCE
  have h1 : Complex.sin (π * (1 + (τ : ℂ) * Complex.I) / 2) = (Real.cosh (π * τ / 2) : ℂ) := by
    rw [show (π : ℂ) * (1 + (τ : ℂ) * Complex.I) / 2 = ((π * τ / 2 : ℝ) : ℂ) * Complex.I + π / 2 by push_cast; ring,
      Complex.sin_add_pi_div_two, Complex.cos_mul_I, ← Complex.ofReal_cosh]
  rw [h1]; push_cast; ring

lemma uctHCE_real {σ : ℝ} :
    uctHCE (σ : ℂ) = ((π ^ 2 / (4 * Real.sin (π * σ / 2) ^ 2) : ℝ) : ℂ) := by
  unfold uctHCE
  rw [show (π : ℂ) * (σ : ℂ) / 2 = ((π * σ / 2 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_sin]
  push_cast; ring

lemma norm_sq_cos_add_mul_I (a b : ℝ) :
    ‖Complex.cos ((a : ℂ) + (b : ℂ) * Complex.I)‖ ^ 2 = Real.cos a ^ 2 + Real.sinh b ^ 2 := by
  rw [Complex.cos_add_mul_I, Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, ← Complex.ofReal_cos, ← Complex.ofReal_cosh, ← Complex.ofReal_sin, ← Complex.ofReal_sinh]
  have h1 := Real.cosh_sq b
  have h2 := Real.sin_sq_add_cos_sq a
  nlinarith [h1, h2]

/-- `(uct:strip-split)` (1), boundary signs and the reflected bound: `H_CE(iτ) = -π²/(4 sinh²(πτ/2)) < 0`, `H_CE(1+iτ) = π²/(4 cosh²(πτ/2)) > 0`,
`H_CE(σ) > 0` and `|H_CE(1-σ-iτ)| ≤ H_CE(1-σ)` for `σ ∈ (0,1)`. -/
theorem uct_HCE_signs :
    (∀ τ : ℝ, τ ≠ 0 → uctHCE ((τ : ℂ) * Complex.I) = ((-(π ^ 2 / (4 * Real.sinh (π * τ / 2) ^ 2)) : ℝ) : ℂ) ∧
      -(π ^ 2 / (4 * Real.sinh (π * τ / 2) ^ 2)) < 0) ∧
    (∀ τ : ℝ, uctHCE (1 + (τ : ℂ) * Complex.I) = ((π ^ 2 / (4 * Real.cosh (π * τ / 2) ^ 2) : ℝ) : ℂ) ∧
      0 < π ^ 2 / (4 * Real.cosh (π * τ / 2) ^ 2)) ∧
    (∀ σ : ℝ, 0 < σ → σ < 1 → 0 < (uctHCE (σ : ℂ)).re ∧ (uctHCE (σ : ℂ)).im = 0) ∧
    (∀ σ : ℝ, 0 < σ → σ < 1 → ∀ τ : ℝ, ‖uctHCE (((1 - σ : ℝ) : ℂ) - (τ : ℂ) * Complex.I)‖ ≤ (uctHCE ((1 - σ : ℝ) : ℂ)).re) := by
  refine ⟨fun τ hτ => ⟨uctHCE_imag τ, ?_⟩, fun τ => ⟨uctHCE_one_add_imag τ, by positivity⟩, fun σ h0 h1 => ?_, fun σ h0 h1 τ => ?_⟩
  · have : Real.sinh (π * τ / 2) ≠ 0 := by
      intro h; rw [Real.sinh_eq_zero] at h
      exact hτ ((mul_eq_zero.mp (by linarith : π * τ = 0)).resolve_left Real.pi_ne_zero)
    have : 0 < π ^ 2 / (4 * Real.sinh (π * τ / 2) ^ 2) := by positivity
    linarith
  · rw [uctHCE_real, Complex.ofReal_re, Complex.ofReal_im]
    refine ⟨?_, rfl⟩
    have : 0 < Real.sin (π * σ / 2) := Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
    positivity
  · set a : ℝ := π * σ / 2 with ha
    set b : ℝ := π * τ / 2 with hb
    have hcos : 0 < Real.cos a := Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
    have h1' : Complex.sin (π * (((1 - σ : ℝ) : ℂ) - (τ : ℂ) * Complex.I) / 2) = Complex.cos ((a : ℂ) + (b : ℂ) * Complex.I) := by
      rw [show (π : ℂ) * (((1 - σ : ℝ) : ℂ) - (τ : ℂ) * Complex.I) / 2 = (π : ℂ) / 2 - ((a : ℂ) + (b : ℂ) * Complex.I) by
        rw [ha, hb]; push_cast; ring, Complex.sin_pi_div_two_sub]
    have hre : (uctHCE ((1 - σ : ℝ) : ℂ)).re = π ^ 2 / (4 * Real.cos a ^ 2) := by
      rw [uctHCE_real, Complex.ofReal_re]
      congr 3
      rw [show π * (1 - σ) / 2 = π / 2 - a by rw [ha]; ring, Real.sin_pi_div_two_sub]
    rw [hre]
    unfold uctHCE
    rw [h1', norm_div, norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    have h4 : ‖(4 : ℂ)‖ = 4 := by simp
    rw [h4]
    have hn := norm_sq_cos_add_mul_I a b
    have hcn : Real.cos a ^ 2 ≤ ‖Complex.cos ((a : ℂ) + (b : ℂ) * Complex.I)‖ ^ 2 := by
      rw [hn]; nlinarith [sq_nonneg (Real.sinh b)]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)

/-- `ℓ'(x) = 1/x - 2/sinh(2x)`, the derivative of `ℓ(x) = log(x coth x)` (`ceEll`). -/
noncomputable def uctEllDeriv (x : ℝ) : ℝ := 1 / x - 2 / Real.sinh (2 * x)

/-- `m'(τ) = (π/2) ℓ'(πτ/2)`, with `m(τ) = ℓ(πτ/2) = log((πτ/2) coth(πτ/2))`. -/
noncomputable def uctMderiv (τ : ℝ) : ℝ := π / 2 * uctEllDeriv (π * τ / 2)

lemma hasDerivAt_uctM {τ : ℝ} (hτ : 0 < τ) : HasDerivAt (fun τ : ℝ => ceEll (π * τ / 2)) (uctMderiv τ) τ := by
  have h1 := ceEll_hasDerivAt (x := π * τ / 2) (by positivity)
  have h2 : HasDerivAt (fun τ : ℝ => π * τ / 2) (π / 2) τ := by
    simpa using ((hasDerivAt_id τ).const_mul π).div_const 2
  have := h1.comp τ h2
  unfold uctMderiv uctEllDeriv
  exact this.congr_deriv (by ring)

/-- Envelope coefficients `(uct:coeffs)`. -/
noncomputable def uctAlphaFl : ℝ := ceK * Real.sqrt ceCs / (2 * π)
noncomputable def uctAlphaOsc : ℝ := |uctCAi| * Real.sqrt (π / 3)
noncomputable def uctAlphaH : ℝ := π ^ (3 / 2 : ℝ) / 4 * |uctCAi|

lemma ceCs_rpow_five_halves : ceCs ^ (5 / 2 : ℝ) = ceCs ^ 2 * Real.sqrt ceCs := by
  rw [show (5 / 2 : ℝ) = 2 + 1 / 2 by norm_num, Real.rpow_add ceCs_pos, Real.rpow_two, Real.sqrt_eq_rpow]

lemma abs_uctCAi : |uctCAi| = 2 * ceK / (Real.sqrt π * ceCs ^ (5 / 2 : ℝ)) := by
  have hs : 0 < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
  have hc : 0 < ceCs ^ (5 / 2 : ℝ) := Real.rpow_pos_of_pos ceCs_pos _
  have h := uctCAi_mul
  have hneg : uctCAi < 0 := by
    by_contra hnn
    have : 0 ≤ uctCAi * ceCs ^ (5 / 2 : ℝ) := mul_nonneg (not_lt.mp hnn) hc.le
    have : 0 < 2 * ceK / Real.sqrt π := by have := ceK_pos; positivity
    linarith
  rw [abs_of_neg hneg]
  have h' : uctCAi * ceCs ^ (5 / 2 : ℝ) * Real.sqrt π = -(2 * ceK) := by rw [h]; field_simp
  field_simp
  linarith

/-- `α_osc = (4√3/π) α_fl`. -/
lemma uctAlphaOsc_eq : uctAlphaOsc = 4 * Real.sqrt 3 / π * uctAlphaFl := by
  have hs : 0 < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
  have h3 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hcs := ceCs_pos
  have hsc : 0 < Real.sqrt ceCs := Real.sqrt_pos.mpr hcs
  have hk := ceK_pos
  have hcube : π ^ 2 = 3 * ceCs ^ 3 := by have := ceCs_cube'; linarith
  unfold uctAlphaOsc uctAlphaFl
  rw [abs_uctCAi, ceCs_rpow_five_halves, Real.sqrt_div (by positivity), div_eq_mul_inv]
  have hsc2 : Real.sqrt ceCs ^ 2 = ceCs := Real.sq_sqrt hcs.le
  field_simp
  rw [hcube]
  rw [hsc2, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]; ring


lemma uctEllDeriv_pos {x : ℝ} (hx : 0 < x) : 0 < uctEllDeriv x := by
  have h := ceEll_deriv_gt hx
  have : 0 < 2 * x / (3 * (1 + x ^ 2 / 3) ^ (3 / 2 : ℝ)) := by positivity
  unfold uctEllDeriv; linarith

/-- The two elementary comparison bounds of `mat:T4(a)` and the Taylor bound for `sinh`, combined:
`12 ℓ³ < (s³ / (1 + t/2)⁴) · (ℓ'² sinh⁴ x)` with `t = x²/3`, `s = √(1+t) ≤ 1 + t/2`. -/
lemma uct_ell_key {x : ℝ} (hx : 0 < x) :
    12 * ceEll x ^ 3 < Real.sqrt (1 + x ^ 2 / 3) ^ 3 / (1 + x ^ 2 / 6) ^ 4 * (uctEllDeriv x ^ 2 * Real.sinh x ^ 4) := by
  set t : ℝ := x ^ 2 / 3 with ht
  have ht0 : 0 < t := by positivity
  set s : ℝ := Real.sqrt (1 + t) with hs
  have hs1 : 1 < s := by rw [hs]; exact Real.lt_sqrt_of_sq_lt (by linarith)
  have hs0 : 0 < s := by linarith
  have hs2 : s ^ 2 = 1 + t := Real.sq_sqrt (by linarith)
  have hs3 : (1 + t) ^ (3 / 2 : ℝ) = s ^ 3 := by
    rw [hs, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
  have hl := ceEll_lt hx
  have hd := ceEll_deriv_gt hx
  rw [← ht, ← hs] at hl
  rw [← ht, hs3] at hd
  have hell0 : 0 < ceEll x := ceEll_pos hx
  have hd0 : 0 < uctEllDeriv x := uctEllDeriv_pos hx
  have hsinh : x * (1 + x ^ 2 / 6) ≤ Real.sinh x := by
    have := sinh_taylor_lower hx.le
    nlinarith [pow_pos hx 5]
  have hp0 : 0 < x * (1 + x ^ 2 / 6) := by positivity
  -- 12 ℓ³ < 12 (x²/(3s))³
  have h1 : ceEll x ^ 3 < (x ^ 2 / (3 * s)) ^ 3 := pow_lt_pow_left₀ hl hell0.le (by norm_num)
  have h2 : (2 * x / (3 * s ^ 3)) ^ 2 * (x * (1 + x ^ 2 / 6)) ^ 4 < uctEllDeriv x ^ 2 * Real.sinh x ^ 4 := by
    have hb : 0 < 2 * x / (3 * s ^ 3) := by positivity
    have e1 : (2 * x / (3 * s ^ 3)) ^ 2 < uctEllDeriv x ^ 2 := pow_lt_pow_left₀ hd hb.le (by norm_num)
    have e2 : (x * (1 + x ^ 2 / 6)) ^ 4 ≤ Real.sinh x ^ 4 := pow_le_pow_left₀ hp0.le hsinh 4
    exact mul_lt_mul e1 e2 (by positivity) (by positivity)
  have hq : (1 + x ^ 2 / 6) = 1 + t / 2 := by rw [ht]; ring
  rw [hq] at h2 ⊢
  have hq0 : 0 < 1 + t / 2 := by positivity
  calc 12 * ceEll x ^ 3 < 12 * (x ^ 2 / (3 * s)) ^ 3 := by linarith
    _ = s ^ 3 / (1 + t / 2) ^ 4 * ((2 * x / (3 * s ^ 3)) ^ 2 * (x * (1 + t / 2)) ^ 4) := by field_simp; ring
    _ < s ^ 3 / (1 + t / 2) ^ 4 * (uctEllDeriv x ^ 2 * Real.sinh x ^ 4) := mul_lt_mul_of_pos_left h2 (by positivity)


lemma uct_ell_key' {x : ℝ} (hx : 0 < x) : 12 * ceEll x ^ 3 < 1 / (1 + x ^ 2 / 6) * (uctEllDeriv x ^ 2 * Real.sinh x ^ 4) := by
  refine (uct_ell_key hx).trans_le ?_
  set t : ℝ := x ^ 2 / 3 with ht
  have ht0 : 0 < t := by positivity
  have hq : (1 + x ^ 2 / 6) = 1 + t / 2 := by rw [ht]; ring
  have hq0 : 0 < 1 + t / 2 := by positivity
  have hs1 : 1 < Real.sqrt (1 + t) := Real.lt_sqrt_of_sq_lt (by linarith)
  have hsle : Real.sqrt (1 + t) ≤ 1 + t / 2 := by
    apply Real.sqrt_le_iff.mpr; constructor <;> nlinarith [sq_nonneg t]
  rw [hq]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  rw [div_le_div_iff₀ (by positivity) hq0]
  have : Real.sqrt (1 + t) ^ 3 ≤ (1 + t / 2) ^ 3 := pow_le_pow_left₀ (by linarith) hsle 3
  nlinarith [this, pow_pos hq0 3]

lemma uct_ell_key_h {x : ℝ} (hx : 0 < x) : 16 * x ^ 2 * ceEll x < 3 * Real.sinh (2 * x) ^ 2 * uctEllDeriv x ^ 2 := by
  set t : ℝ := x ^ 2 / 3 with ht
  have ht0 : 0 < t := by positivity
  set s : ℝ := Real.sqrt (1 + t) with hs
  have hs1 : 1 < s := by rw [hs]; exact Real.lt_sqrt_of_sq_lt (by linarith)
  have hs0 : 0 < s := by linarith
  have hs2 : s ^ 2 = 1 + t := Real.sq_sqrt (by linarith)
  have hs3 : (1 + t) ^ (3 / 2 : ℝ) = s ^ 3 := by
    rw [hs, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
  have hl := ceEll_lt hx
  have hd := ceEll_deriv_gt hx
  rw [← ht, ← hs] at hl
  rw [← ht, hs3] at hd
  have hsle : s ≤ 1 + t / 2 := by
    rw [hs]; apply Real.sqrt_le_iff.mpr; constructor <;> nlinarith [sq_nonneg t]
  set P : ℝ := 1 + 2 * t + 6 / 5 * t ^ 2 with hP
  have hP0 : 0 < P := by positivity
  have hsinh : 2 * x * P ≤ Real.sinh (2 * x) := by
    have h := sinh_taylor_lower (by linarith : 0 ≤ 2 * x)
    have e : 2 * x * P = 2 * x + (2 * x) ^ 3 / 6 + (2 * x) ^ 5 / 120 := by rw [hP, ht]; ring
    linarith
  have h5 : s ^ 5 ≤ P ^ 2 := by
    have e1 : s ^ 5 = (1 + t) ^ 2 * s := by rw [← hs2]; ring
    have e2 : P ^ 2 - (1 + t) ^ 2 * (1 + t / 2) = 3 / 2 * t + 22 / 5 * t ^ 2 + 43 / 10 * t ^ 3 + 36 / 25 * t ^ 4 := by rw [hP]; ring
    have e3 : (1 + t) ^ 2 * s ≤ (1 + t) ^ 2 * (1 + t / 2) := mul_le_mul_of_nonneg_left hsle (by positivity)
    have : 0 ≤ 3 / 2 * t + 22 / 5 * t ^ 2 + 43 / 10 * t ^ 3 + 36 / 25 * t ^ 4 := by positivity
    rw [e1]; linarith
  have hd0 : 0 < 2 * x / (3 * s ^ 3) := by positivity
  have e1 : (2 * x / (3 * s ^ 3)) ^ 2 < uctEllDeriv x ^ 2 := pow_lt_pow_left₀ hd hd0.le (by norm_num)
  have e2 : (2 * x * P) ^ 2 ≤ Real.sinh (2 * x) ^ 2 := pow_le_pow_left₀ (by positivity) hsinh 2
  have hmid : 16 * x ^ 4 / (3 * s) ≤ 3 * (2 * x * P) ^ 2 * (2 * x / (3 * s ^ 3)) ^ 2 := by
    have : 3 * (2 * x * P) ^ 2 * (2 * x / (3 * s ^ 3)) ^ 2 = 16 * x ^ 4 * P ^ 2 / (3 * s ^ 6) := by field_simp; ring
    rw [this, div_le_div_iff₀ (by positivity) (by positivity)]
    have : 16 * x ^ 4 * (3 * s ^ 6) = 16 * x ^ 4 * 3 * s * s ^ 5 := by ring
    rw [this]
    have : 16 * x ^ 4 * P ^ 2 * (3 * s) = 16 * x ^ 4 * 3 * s * P ^ 2 := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left h5 (by positivity)
  calc 16 * x ^ 2 * ceEll x < 16 * x ^ 2 * (x ^ 2 / (3 * s)) := by gcongr
    _ = 16 * x ^ 4 / (3 * s) := by field_simp
    _ ≤ 3 * (2 * x * P) ^ 2 * (2 * x / (3 * s ^ 3)) ^ 2 := hmid
    _ < 3 * Real.sinh (2 * x) ^ 2 * uctEllDeriv x ^ 2 := by
        have hsp : 0 < Real.sinh (2 * x) := lt_of_lt_of_le (by positivity) hsinh
        exact mul_lt_mul' (by gcongr) e1 (by positivity) (by positivity)


lemma tau0_ceEll {τ : ℝ} (hτ : 0 < τ) : tau0 (ceEll (π * τ / 2)) = τ := by
  have hL : 0 < ceEll (π * τ / 2) := ceEll_pos (by positivity)
  exact (existsUnique_tau0 hL).unique ⟨tau0_pos hL, ceEll_tau0 hL⟩ ⟨hτ, rfl⟩

lemma uctAlphaH_eq : uctAlphaH = π * Real.sqrt 3 / 4 * uctAlphaOsc := by
  have h3 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hs : 0 < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
  unfold uctAlphaH uctAlphaOsc
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add Real.pi_pos, Real.rpow_one, ← Real.sqrt_eq_rpow,
    Real.sqrt_div Real.pi_pos.le]
  field_simp

lemma uctAlphaFl_pos : 0 < uctAlphaFl := by
  unfold uctAlphaFl; have := ceK_pos; have := ceCs_pos; positivity

lemma uctAlphaOsc_pos : 0 < uctAlphaOsc := by
  rw [uctAlphaOsc_eq]; have := uctAlphaFl_pos; positivity

lemma uctAlphaH_pos : 0 < uctAlphaH := by
  rw [uctAlphaH_eq]; have := uctAlphaOsc_pos; positivity

/-- The envelopes `(uct:envelopes)`. -/
noncomputable def uctIfl (L : ℝ) : ℝ := uctAlphaFl * L ^ (-(3 / 2 : ℝ))
noncomputable def uctIoscStar (L : ℝ) : ℝ := uctAlphaOsc * ‖uctHstar ((tau0 L : ℂ) * Complex.I)‖ / uctMderiv (tau0 L)
noncomputable def uctIoscCE (L : ℝ) : ℝ := uctAlphaOsc * ‖uctHCE ((tau0 L : ℂ) * Complex.I)‖ / uctMderiv (tau0 L)
noncomputable def uctIoscH (L : ℝ) : ℝ := uctAlphaOsc * (uctHCE (1 + (tau0 L : ℂ) * Complex.I)).re / uctMderiv (tau0 L)
noncomputable def uctIflH (L : ℝ) : ℝ := uctAlphaH * L ^ (-(1 / 2 : ℝ)) * Real.exp (-L)

lemma norm_uctHCE_imag {τ : ℝ} (hτ : 0 < τ) : ‖uctHCE ((τ : ℂ) * Complex.I)‖ = π ^ 2 / (4 * Real.sinh (π * τ / 2) ^ 2) := by
  rw [uctHCE_imag, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos]
  have : 0 < Real.sinh (π * τ / 2) := Real.sinh_pos_iff.mpr (by positivity)
  positivity

lemma uctHCE_one_add_imag_re (τ : ℝ) : (uctHCE (1 + (τ : ℂ) * Complex.I)).re = π ^ 2 / (4 * Real.cosh (π * τ / 2) ^ 2) := by
  rw [uctHCE_one_add_imag, Complex.ofReal_re]

lemma uctIoscCE_div {τ : ℝ} (hτ : 0 < τ) :
    uctIoscCE (ceEll (π * τ / 2)) / uctIfl (ceEll (π * τ / 2)) =
      2 * Real.sqrt 3 * ceEll (π * τ / 2) ^ (3 / 2 : ℝ) / (uctEllDeriv (π * τ / 2) * Real.sinh (π * τ / 2) ^ 2) := by
  have hx : 0 < π * τ / 2 := by positivity
  set x := π * τ / 2 with hxdef
  have hd := uctEllDeriv_pos hx
  have hsh : 0 < Real.sinh x := Real.sinh_pos_iff.mpr hx
  have hl := ceEll_pos hx
  have hl32 : 0 < ceEll x ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hl _
  have hfl := uctAlphaFl_pos
  unfold uctIoscCE uctIfl
  rw [tau0_ceEll hτ, norm_uctHCE_imag hτ, uctAlphaOsc_eq, Real.rpow_neg hl.le]
  unfold uctMderiv
  rw [← hxdef]
  have h3 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  field_simp

lemma exp_ceEll {x : ℝ} (hx : 0 < x) : Real.exp (ceEll x) = x * Real.cosh x / Real.sinh x := by
  unfold ceEll
  rw [Real.exp_log (div_pos hx (tanh_pos_of_pos hx)), Real.tanh_eq_sinh_div_cosh]
  have : 0 < Real.sinh x := Real.sinh_pos_iff.mpr hx
  have := Real.cosh_pos x
  field_simp

lemma uctIoscH_div {τ : ℝ} (hτ : 0 < τ) :
    uctIoscH (ceEll (π * τ / 2)) / uctIflH (ceEll (π * τ / 2)) =
      4 * (π * τ / 2) * Real.sqrt (ceEll (π * τ / 2)) / (Real.sqrt 3 * Real.sinh (2 * (π * τ / 2)) * uctEllDeriv (π * τ / 2)) := by
  have hx : 0 < π * τ / 2 := by positivity
  set x := π * τ / 2 with hxdef
  have hd := uctEllDeriv_pos hx
  have hsh : 0 < Real.sinh x := Real.sinh_pos_iff.mpr hx
  have hch := Real.cosh_pos x
  have hl := ceEll_pos hx
  have hsl : 0 < Real.sqrt (ceEll x) := Real.sqrt_pos.mpr hl
  have hfl := uctAlphaFl_pos
  have h3 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  unfold uctIoscH uctIflH
  rw [tau0_ceEll hτ, uctHCE_one_add_imag_re, uctAlphaH_eq, Real.rpow_neg hl.le, ← Real.sqrt_eq_rpow, Real.exp_neg, exp_ceEll hx,
    Real.sinh_two_mul]
  unfold uctMderiv
  rw [← hxdef]
  have hA := uctAlphaOsc_pos
  field_simp
  norm_num


lemma uctRce_sq_lt {x : ℝ} (hx : 0 < x) :
    0 < 2 * Real.sqrt 3 * ceEll x ^ (3 / 2 : ℝ) / (uctEllDeriv x * Real.sinh x ^ 2) ∧
      (2 * Real.sqrt 3 * ceEll x ^ (3 / 2 : ℝ) / (uctEllDeriv x * Real.sinh x ^ 2)) ^ 2 < 1 / (1 + x ^ 2 / 6) := by
  have hd := uctEllDeriv_pos hx
  have hsh : 0 < Real.sinh x := Real.sinh_pos_iff.mpr hx
  have hl := ceEll_pos hx
  have h3 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  refine ⟨by positivity, ?_⟩
  have hl2 : (ceEll x ^ (3 / 2 : ℝ)) ^ 2 = ceEll x ^ 3 := by
    rw [← Real.rpow_natCast (ceEll x ^ (3 / 2 : ℝ)) 2, ← Real.rpow_mul hl.le]; norm_num
  have e : (2 * Real.sqrt 3 * ceEll x ^ (3 / 2 : ℝ) / (uctEllDeriv x * Real.sinh x ^ 2)) ^ 2 =
      12 * ceEll x ^ 3 / (uctEllDeriv x ^ 2 * Real.sinh x ^ 4) := by
    rw [div_pow, mul_pow, mul_pow, hl2, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    ring
  rw [e, div_lt_iff₀ (by positivity)]
  have := uct_ell_key' hx
  linarith

lemma uctRh_lt {x : ℝ} (hx : 0 < x) :
    4 * x * Real.sqrt (ceEll x) / (Real.sqrt 3 * Real.sinh (2 * x) * uctEllDeriv x) < 1 := by
  have hd := uctEllDeriv_pos hx
  have hsh : 0 < Real.sinh (2 * x) := Real.sinh_pos_iff.mpr (by linarith)
  have hl := ceEll_pos hx
  have h3 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  rw [div_lt_one (by positivity)]
  have hk := uct_ell_key_h hx
  have hA : (4 * x * Real.sqrt (ceEll x)) ^ 2 = 16 * x ^ 2 * ceEll x := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hl.le]; ring
  have hB : (Real.sqrt 3 * Real.sinh (2 * x) * uctEllDeriv x) ^ 2 = 3 * Real.sinh (2 * x) ^ 2 * uctEllDeriv x ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  exact lt_of_pow_lt_pow_left₀ 2 (by positivity) (by rw [hA, hB]; exact hk)

/-- **`(uct:global-ratios)` (3)** of `uct:strip-split`: for every `τ > 0` and `L = m(τ) = ℓ(πτ/2)`,
`r_CE(τ) = I_osc^CE(L)/I_fl(L) < 1` and `r_ĥ(τ;1) = I_osc^ĥ(L)/I_fl^ĥ(L) < 1`; and the quantitative form
`1 - r_CE(τ₀(L)) ≥ (1/6) min(L, 1)` for all `L > 0` (so `c_r = 1/6`).  The expansions of `r_CE`, `r_ĥ` at `τ ↓ 0` are not part of this declaration. -/
theorem uct_strip_split_ratios :
    (∀ τ : ℝ, 0 < τ →
      uctIoscCE (ceEll (π * τ / 2)) / uctIfl (ceEll (π * τ / 2)) < 1 ∧
        uctIoscH (ceEll (π * τ / 2)) / uctIflH (ceEll (π * τ / 2)) < 1) ∧
      ∀ L : ℝ, 0 < L → (1 / 6 : ℝ) * min L 1 ≤ 1 - uctIoscCE L / uctIfl L := by
  have hlt : ∀ x : ℝ, 0 < x → ∀ r : ℝ, 0 < r → r ^ 2 < 1 / (1 + x ^ 2 / 6) → r < 1 := by
    intro x hx r hr h
    have h1 : 1 / (1 + x ^ 2 / 6) ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith [sq_nonneg x]
    by_contra hcon
    have : 1 ≤ r ^ 2 := by nlinarith [not_lt.mp hcon]
    linarith
  refine ⟨fun τ hτ => ⟨?_, ?_⟩, fun L hL => ?_⟩
  · rw [uctIoscCE_div hτ]
    obtain ⟨h0, h1⟩ := uctRce_sq_lt (show 0 < π * τ / 2 by positivity)
    exact hlt _ (by positivity) _ h0 h1
  · rw [uctIoscH_div hτ]
    exact uctRh_lt (by positivity)
  · have hτ := tau0_pos hL
    have hx : 0 < π * tau0 L / 2 := by positivity
    set x := π * tau0 L / 2 with hxdef
    have hLx : ceEll x = L := ceEll_tau0 hL
    have hdiv := uctIoscCE_div hτ
    rw [← hxdef, hLx] at hdiv
    rw [hdiv]
    obtain ⟨h0, h1⟩ := uctRce_sq_lt hx
    rw [hLx] at h0 h1
    set r := 2 * Real.sqrt 3 * L ^ (3 / 2 : ℝ) / (uctEllDeriv x * Real.sinh x ^ 2) with hr
    have hr1 : r < 1 := hlt x hx r h0 h1
    set t : ℝ := x ^ 2 / 3 with ht
    have ht0 : 0 < t := by positivity
    have hq : 1 + x ^ 2 / 6 = 1 + t / 2 := by rw [ht]; ring
    rw [hq] at h1
    have hLt : L ≤ t := by rw [← hLx]; exact (ceEll_lt_sq_div_three hx).le
    -- 1 - r ≥ (1 - r²)/2 > (1 - 1/(1+t/2))/2 = t / (4 + 2t) ≥ min(t,1)/6
    have h2 : (1 - 1 / (1 + t / 2)) / 2 ≤ 1 - r := by nlinarith [h1, h0, hr1]
    have h3 : (1 - 1 / (1 + t / 2)) / 2 = t / (4 + 2 * t) := by field_simp; ring
    rw [h3] at h2
    have h4 : (1 / 6 : ℝ) * min t 1 ≤ t / (4 + 2 * t) := by
      rw [le_div_iff₀ (by positivity)]
      rcases le_total t 1 with h | h
      · rw [min_eq_left h]; nlinarith
      · rw [min_eq_right h]; nlinarith
    have h5 : min L 1 ≤ min t 1 := min_le_min hLt le_rfl
    linarith

/-- info: 'FormalResearch.SignUncertainty.uct_H_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uct_H_split

/-- info: 'FormalResearch.SignUncertainty.uct_HCE_signs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uct_HCE_signs

/-- info: 'FormalResearch.SignUncertainty.hasDerivAt_uctM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasDerivAt_uctM

/-- info: 'FormalResearch.SignUncertainty.uctAlphaOsc_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uctAlphaOsc_eq

/-- info: 'FormalResearch.SignUncertainty.uctAlphaH_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uctAlphaH_eq

/-- info: 'FormalResearch.SignUncertainty.uct_strip_split_ratios' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uct_strip_split_ratios

end FormalResearch.SignUncertainty
