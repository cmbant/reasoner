/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctInnerSymbolsRot

/-!
# Lemma `fct:inner-symbols` (FCT.5b) (a), closed form: the initial values at `û = 0`

Paper I (`constant_terms_five.tex`), Lemma `fct:inner-symbols` (a), last sentence.  At `û = 0` and `κ = u^j` the regularised integral is
`e^{-iπ/4} ∫_0^∞ t^{s-1} e^{-i t³/12 - ε t²} dt` with `s = j + 1/2`; the contour rotation `FctRot.rot_tendsto` gives the Abel limit
`e^{-iπ/4 - iπ s/6} ∫_0^∞ t^{s-1} e^{-t³/12} dt = e^{-iπ/4 - iπ s/6} (1/3) 12^{s/3} Γ(s/3)` (`fctSLimit_zero_pow`), which is compared with
`i^j (-2√π) conj(G_j(0))` (`CtAiry.gI_zero`) for `j = 0, 1, 2`.

Proved: `fctInnerSymbolsG0Init : FctInnerSymbolsG0Init`, and hence (`fctInnerSymbolsG0_of_init`) the unconditional
`fctInnerSymbolsG0 : FctInnerSymbolsG0`, `𝒮[1] = G_0 = 2π^{3/2}(Ai² - i Ai Bi)`.

Class: proved.
-/
@[expose] public section

open Set Filter Topology MeasureTheory
open scoped Real

namespace FormalResearch.SignUncertainty

namespace FctSymA

/-- At `û = 0` and `κ = u^j` the regularised integral is the rotated-contour integral at `θ = 0`, `s = j + 1/2`, `a = 1/12`. -/
lemma fctSEps_zero_pow (j : ℕ) (ε : ℝ) :
    fctSEps 0 ε (fun u => (u : ℂ) ^ j) =
      Complex.exp (((-(π / 4) : ℝ) : ℂ) * Complex.I) * FctRot.rotI ((j : ℝ) + 1 / 2) (1 / 12) ε 0 := by
  unfold fctSEps FctRot.rotI
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
  have hu0 : 0 < u := hu
  have hpow : u ^ ((j : ℝ) + 1 / 2 - 1) = u ^ (-(1 / 2 : ℝ)) * u ^ j := by
    rw [show (j : ℝ) + 1 / 2 - 1 = -(1 / 2 : ℝ) + (j : ℕ) by ring, Real.rpow_add hu0, Real.rpow_natCast]
  have hE : Complex.exp (-(Complex.I * (((0 : ℝ) * u + u ^ 3 / 12 : ℝ) : ℂ)) - ((ε * u ^ 2 : ℝ) : ℂ)) =
      Complex.exp (FctRot.rotE ((j : ℝ) + 1 / 2) (1 / 12) ε 0 u) := by
    congr 1
    unfold FctRot.rotE
    simp only [Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, mul_one]
    push_cast
    ring
  unfold FctRot.rotF
  rw [hE, hpow]
  push_cast
  ring

/-- The Gamma value of `∫_0^∞ t^{s-1} e^{-a t³} dt`. -/
lemma integral_rot_gamma {s a : ℝ} (hs : 0 < s) (ha : 0 < a) :
    ∫ t in Ioi (0 : ℝ), (((t ^ (s - 1) * Real.exp (-(a * t ^ 3)) : ℝ) : ℂ)) =
      ((a ^ (-s / 3) * (1 / 3) * Real.Gamma (s / 3) : ℝ) : ℂ) := by
  rw [integral_complex_ofReal]
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 3) (q := s - 1) (b := a) (by norm_num) (by linarith) ha
  have e : ∀ t ∈ Ioi (0 : ℝ), t ^ (s - 1) * Real.exp (-(a * t ^ 3)) = t ^ (s - 1) * Real.exp (-a * t ^ (3 : ℝ)) := by
    intro t _
    have h3 : t ^ (3 : ℝ) = t ^ 3 := by exact_mod_cast Real.rpow_natCast t 3
    rw [h3, neg_mul]
  rw [setIntegral_congr_fun measurableSet_Ioi e, h]
  congr 2 <;> ring_nf

/-- **Abel limit at `û = 0`, `κ = u^j`:**  `𝒮[u^j](0) = e^{-iπ/4} e^{-iπ s/6} (1/3) 12^{s/3} Γ(s/3)`, `s = j + 1/2`. -/
theorem fctSLimit_zero_pow (j : ℕ) :
    FctSLimit 0 (fun u => (u : ℂ) ^ j)
      (Complex.exp (((-(π / 4) : ℝ) : ℂ) * Complex.I) *
        (Complex.exp (-(Complex.I * ((π / 6 * ((j : ℝ) + 1 / 2) : ℝ) : ℂ))) *
          ((((1 / 12 : ℝ)) ^ (-((j : ℝ) + 1 / 2) / 3) * (1 / 3) * Real.Gamma (((j : ℝ) + 1 / 2) / 3) : ℝ) : ℂ))) := by
  have hs : (0 : ℝ) < (j : ℝ) + 1 / 2 := by positivity
  have := (FctRot.rot_tendsto hs (by norm_num : (0 : ℝ) < 1 / 12)).const_mul
    (Complex.exp (((-(π / 4) : ℝ) : ℂ) * Complex.I))
  rw [integral_rot_gamma hs (by norm_num)] at this
  unfold FctSLimit
  simp_rw [fctSEps_zero_pow]
  exact this

end FctSymA

section values

open CtAiry

lemma rr_mul_two_rpow (y : ℝ) : rr * (2 : ℝ) ^ y = (2 : ℝ) ^ (y - 1 / 3) := by
  unfold rr
  rw [← Real.rpow_add (by norm_num)]; ring_nf

lemma inv_twelve_rpow (y : ℝ) : ((1 / 12 : ℝ)) ^ (-y) = (2 : ℝ) ^ (2 * y) * (3 : ℝ) ^ y := by
  rw [one_div, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num), neg_neg,
    show (12 : ℝ) = (2 : ℝ) ^ (2 : ℝ) * 3 by norm_num, Real.mul_rpow (by positivity) (by norm_num),
    ← Real.rpow_mul (by norm_num)]

lemma star_al : star al = ⟨-rr, -(rr * √3)⟩ := by
  apply Complex.ext <;> simp [al]

lemma exp_neg_I (x : ℝ) :
    Complex.exp (-(Complex.I * (x : ℂ))) = ((Real.cos x : ℝ) : ℂ) - Complex.I * ((Real.sin x : ℝ) : ℂ) := by
  rw [show -(Complex.I * (x : ℂ)) = ((-x : ℝ) : ℂ) * Complex.I by push_cast; ring, Complex.exp_mul_I]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
  push_cast
  ring

/-- The combined phase `e^{-iπ/4} e^{-iπ s/6} = e^{-i c}` when `c = π/4 + π s/6`. -/
lemma phase_comb (s c : ℝ) (h : π / 4 + π / 6 * s = c) :
    Complex.exp (((-(π / 4) : ℝ) : ℂ) * Complex.I) * Complex.exp (-(Complex.I * ((π / 6 * s : ℝ) : ℂ))) =
      Complex.exp (-(Complex.I * (c : ℂ))) := by
  rw [← Complex.exp_add, ← h]
  congr 1
  push_cast; ring

/-- `𝒮[u](0) = i · (-2√π) · conj(G_1(0))`. -/
lemma init1 : fctS 0 (fun u => (u : ℂ) ^ 1) = Complex.I * ((-(2 * ((√π : ℝ) : ℂ))) * star (G1 0)) := by
  rw [(FctSymA.fctSLimit_zero_pow 1).fctS_eq]
  rw [← mul_assoc, phase_comb _ (π / 2) (by push_cast; ring), exp_neg_I, Real.cos_pi_div_two, Real.sin_pi_div_two]
  unfold G1
  rw [gI_zero (by norm_num)]
  have hπ : (0 : ℝ) < √π := Real.sqrt_pos.2 Real.pi_pos
  rw [show (-(((1 : ℕ) : ℝ) + 1 / 2) / 3 : ℝ) = -(1 / 2) by norm_num, inv_twelve_rpow,
    show ((((1 : ℕ) : ℝ) + 1 / 2) / 3 : ℝ) = 1 / 2 by norm_num, show ((1 / 2 : ℝ) + 1) / 3 = 1 / 2 by norm_num,
    Real.Gamma_one_half_eq, show (2 * (1 / 2 : ℝ)) = 1 by norm_num, Real.rpow_one]
  have hπc : ((√π : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hπ.ne'
  simp only [star_div₀, Complex.star_def, Complex.conj_ofReal]
  push_cast
  field_simp
  ring

/-- `𝒮[1](0) = -2√π · conj(G_0(0))`. -/
lemma init0 : fctS 0 (fun u => (u : ℂ) ^ 0) = (-(2 * ((√π : ℝ) : ℂ))) * star (G0 0) := by
  rw [(FctSymA.fctSLimit_zero_pow 0).fctS_eq]
  rw [← mul_assoc, phase_comb _ (π / 3) (by push_cast; ring), exp_neg_I, Real.cos_pi_div_three, Real.sin_pi_div_three]
  unfold G0
  rw [gI_zero (by norm_num)]
  have hπ : (0 : ℝ) < √π := Real.sqrt_pos.2 Real.pi_pos
  rw [show (-(((0 : ℕ) : ℝ) + 1 / 2) / 3 : ℝ) = -(1 / 6) by norm_num, inv_twelve_rpow,
    show ((((0 : ℕ) : ℝ) + 1 / 2) / 3 : ℝ) = 1 / 6 by norm_num, show ((-1 / 2 : ℝ) + 1) / 3 = 1 / 6 by norm_num]
  have hrx : rr * (2 : ℝ) ^ (2 * (1 / 6 : ℝ)) = 1 := by
    rw [rr_mul_two_rpow]; norm_num
  have hπc : ((√π : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hπ.ne'
  have hal : (starRingEnd ℂ) al = ⟨-rr, -(rr * √3)⟩ := by apply Complex.ext <;> simp [al]
  have hA : (starRingEnd ℂ) al ≠ 0 := by simpa using al_ne
  have h3 : (√3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have key : (((1 / 2 : ℝ) : ℂ) - Complex.I * ((√3 / 2 : ℝ) : ℂ)) * (starRingEnd ℂ) al = -(2 * (rr : ℂ)) := by
    rw [hal]
    apply Complex.ext
    · simp; linear_combination (-(rr) / 2) * h3
    · simp; ring
  simp only [star_div₀, star_mul', Complex.star_def, Complex.conj_ofReal]
  generalize (2 : ℝ) ^ (2 * (1 / 6 : ℝ)) = x at hrx ⊢
  generalize (3 : ℝ) ^ (1 / 6 : ℝ) = a3
  generalize Real.Gamma (1 / 6) = g
  generalize (starRingEnd ℂ) al = A at hA key
  have hrxc : (rr : ℂ) * (x : ℂ) = 1 := by exact_mod_cast hrx
  have hω : (((1 / 2 : ℝ) : ℂ) - Complex.I * ((√3 / 2 : ℝ) : ℂ)) = -(2 * (rr : ℂ)) / A := by
    rw [eq_div_iff hA]; exact key
  rw [hω]
  push_cast
  field_simp
  linear_combination (-(a3 : ℂ) * g) * hrxc

/-- `𝒮[u²](0) = i² · (-2√π) · conj(G_2(0))`. -/
lemma init2 : fctS 0 (fun u => (u : ℂ) ^ 2) = Complex.I ^ 2 * ((-(2 * ((√π : ℝ) : ℂ))) * star (G2 0)) := by
  rw [(FctSymA.fctSLimit_zero_pow 2).fctS_eq]
  rw [← mul_assoc, phase_comb _ (π - π / 3) (by push_cast; ring), exp_neg_I, Real.cos_pi_sub, Real.sin_pi_sub,
    Real.cos_pi_div_three, Real.sin_pi_div_three]
  unfold G2
  rw [gI_zero (by norm_num)]
  have hπ : (0 : ℝ) < √π := Real.sqrt_pos.2 Real.pi_pos
  rw [show (-(((2 : ℕ) : ℝ) + 1 / 2) / 3 : ℝ) = -(5 / 6) by norm_num, inv_twelve_rpow,
    show ((((2 : ℕ) : ℝ) + 1 / 2) / 3 : ℝ) = 5 / 6 by norm_num, show ((3 / 2 : ℝ) + 1) / 3 = 5 / 6 by norm_num]
  have hx : (2 : ℝ) ^ (2 * (5 / 6 : ℝ)) = 4 * rr := by
    unfold rr
    rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) by norm_num, ← Real.rpow_add (by norm_num)]
    norm_num
  have hπc : ((√π : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hπ.ne'
  have hal : (starRingEnd ℂ) al = ⟨-rr, -(rr * √3)⟩ := by apply Complex.ext <;> simp [al]
  have hrr : (rr : ℂ) ≠ 0 := by exact_mod_cast rr_pos.ne'
  have h3 : (√3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have key : (((-(1 / 2) : ℝ) : ℂ) - Complex.I * ((√3 / 2 : ℝ) : ℂ)) * (2 * (rr : ℂ)) = (starRingEnd ℂ) al := by
    rw [hal]
    apply Complex.ext
    · simp
    · simp; ring
  simp only [star_div₀, star_mul', Complex.star_def, Complex.conj_ofReal]
  generalize (2 : ℝ) ^ (2 * (5 / 6 : ℝ)) = x at hx ⊢
  generalize (3 : ℝ) ^ (5 / 6 : ℝ) = a3
  generalize Real.Gamma (5 / 6) = g
  generalize (starRingEnd ℂ) al = A at key
  have hω : (((-(1 / 2) : ℝ) : ℂ) - Complex.I * ((√3 / 2 : ℝ) : ℂ)) = A / (2 * (rr : ℂ)) := by
    rw [eq_div_iff (mul_ne_zero two_ne_zero hrr)]; exact key
  have hxc : (x : ℂ) = 4 * (rr : ℂ) := by exact_mod_cast hx
  rw [hω]
  push_cast
  rw [hxc]
  field_simp
  ring_nf
  simp only [Complex.I_sq]
  ring

end values

/-- **Initial values of `fct:inner-symbols` (a), closed form** (proved; the former named input `FctInnerSymbolsG0Init`): `𝒮[u^j](0) = i^j (-2√π) conj(G_j(0))`,
`j = 0, 1, 2`.  Proof: contour rotation `arg u = -π/6` of the `ε`-regularised integral (`FctRot.rot_tendsto`), Gamma integrals, algebra with `CtAiry.gI_zero`. -/
theorem fctInnerSymbolsG0Init : FctInnerSymbolsG0Init := ⟨init0, init1, init2⟩

/-- **`fct:inner-symbols` (a), closed form `𝒮[1] = G_0 = 2π^{3/2}(Ai² - i Ai Bi)` on the real line** (proved, unconditional): `fctInnerSymbolsG0_of_init` with the initial
values `fctInnerSymbolsG0Init`. -/
theorem fctInnerSymbolsG0 : FctInnerSymbolsG0 := fctInnerSymbolsG0_of_init fctInnerSymbolsG0Init

/-- info: 'FormalResearch.SignUncertainty.fctInnerSymbolsG0Init' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctInnerSymbolsG0Init

/-- info: 'FormalResearch.SignUncertainty.fctInnerSymbolsG0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctInnerSymbolsG0

end FormalResearch.SignUncertainty
