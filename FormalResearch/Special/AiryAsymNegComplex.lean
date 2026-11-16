module

public import FormalResearch.Special.AiryAsymSector
public import FormalResearch.Special.AiryAsymNeg

/-!
# `Ai` near the negative axis: the complex two-exponential asymptotics with remainder

For `q ∈ ℂ` in the sector `|arg q| ≤ π/6` (`Re q ≥ (√3/2)‖q‖`) put `z = -q²` (so `z` runs over
`|arg z| ≥ 2π/3`, a neighbourhood of the negative axis; `q = (-z)^{1/2}`) and `ξ = (2/3) q³`
(`= (2/3)(-z)^{3/2}`, a complex phase).  With `ε = e^{iπ/6}`, `ω = e^{2πi/3}` one has
`ωz = (ε̄ q)²`, `ω²z = (ε q)²`, both with `Re(ε^{±1} q) ≥ ‖q‖/2`, so the sector estimate of
`AiryAsymSector` applies with `s = 1/2` to both terms of the rotation identity
`Ai(z) = -ω Ai(ωz) - ω² Ai(ω²z)`.  The two leading terms `e^{±iξ}` combine into a cosine:

* `airyAiC_neg_complex` (DLMF 9.7.9 in a complex neighbourhood of the negative axis, explicit remainder):
  `‖Ai(-q²) - (1/π) (π/q)^{1/2} cos(ξ - π/4)‖ ≤ (6/5) e^{|Im ξ|} (√(π/‖q‖)/π) / ‖q‖³`,
  where `(π/q)^{1/2}` is the principal root, `‖(π/q)^{1/2}‖ = √(π/‖q‖)`; in terms of `r = ‖z‖ = ‖q‖²`
  the relative remainder is `O(r^{-3/2})` times `e^{|Im ξ|}`, the size of `cos(ξ - π/4)` away from its zeros.
  Numerical check (mpmath, 25 digits; `‖q‖ ∈ {0.5,…,40}`, 61 angles across `|arg q| ≤ π/6`): the true error is at
  most `0.087` times the stated bound.

The derivation uses no branch computation beyond `Re(e^{±iπ/12} τ) > 0` for `τ = (π/q)^{1/2}`
(which follows from `Re τ² > 0`).  The derivative analogue is `deriv_airyAiC_neg_complex` (`AiryCft2DerivNeg`).  Not formalised: the `Bi` combination.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.Special

/-! ### Algebra of `ε^{±1} q` -/

lemma airyRe_eps_mul (q : ℂ) : (airyEps * q).re = √3 / 2 * q.re - 1 / 2 * q.im := by
  simp [airyEps, Complex.mul_re]

lemma airyRe_conj_eps_mul (q : ℂ) :
    ((starRingEnd ℂ) airyEps * q).re = √3 / 2 * q.re + 1 / 2 * q.im := by
  simp [airyEps, Complex.mul_re]

lemma airyNorm_eps_mul (q : ℂ) : ‖airyEps * q‖ = ‖q‖ := by
  rw [norm_mul, norm_airyEps, one_mul]

lemma airyNorm_conj_eps_mul (q : ℂ) : ‖(starRingEnd ℂ) airyEps * q‖ = ‖q‖ := by
  rw [norm_mul, norm_conj_airyEps, one_mul]

/-- The sector hypothesis on `q`: `|arg q| ≤ π/6`. -/
def NegSector (q : ℂ) : Prop := √3 / 2 * ‖q‖ ≤ q.re

lemma NegSector.re_nonneg {q : ℂ} (h : NegSector q) : 0 ≤ q.re :=
  le_trans (by positivity) h

lemma NegSector.abs_im_le {q : ℂ} (h : NegSector q) : |q.im| ≤ ‖q‖ / 2 := by
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  have e := sq_norm_eq q
  have h1 : (√3 / 2 * ‖q‖) ^ 2 ≤ q.re ^ 2 := pow_le_pow_left₀ (by positivity) h 2
  have : q.im ^ 2 ≤ (‖q‖ / 2) ^ 2 := by nlinarith
  exact abs_le_of_sq_le_sq' this (by positivity) |> fun h => abs_le.mpr h

lemma NegSector.re_eps {q : ℂ} (h : NegSector q) : ‖q‖ / 2 ≤ (airyEps * q).re := by
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  have := abs_le.mp h.abs_im_le
  rw [airyRe_eps_mul]
  have h' : √3 / 2 * (√3 / 2 * ‖q‖) ≤ √3 / 2 * q.re := mul_le_mul_of_nonneg_left h (by positivity)
  have h4 : √3 / 2 * (√3 / 2 * ‖q‖) = 3 / 4 * ‖q‖ := by
    rw [← mul_assoc, show √3 / 2 * (√3 / 2) = 3 / 4 by nlinarith]
  linarith

lemma NegSector.re_conj_eps {q : ℂ} (h : NegSector q) : ‖q‖ / 2 ≤ ((starRingEnd ℂ) airyEps * q).re := by
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  have := abs_le.mp h.abs_im_le
  rw [airyRe_conj_eps_mul]
  have h' : √3 / 2 * (√3 / 2 * ‖q‖) ≤ √3 / 2 * q.re := mul_le_mul_of_nonneg_left h (by positivity)
  have h4 : √3 / 2 * (√3 / 2 * ‖q‖) = 3 / 4 * ‖q‖ := by
    rw [← mul_assoc, show √3 / 2 * (√3 / 2) = 3 / 4 by nlinarith]
  linarith

/-! ### Rotation identity at `z = -q²` -/

lemma airyConj_eps_sq : ((starRingEnd ℂ) airyEps) ^ 2 = -airyOmega := by
  rw [← map_pow, airyEps_sq, map_neg, conj_airyOmega_sq]

lemma airyConj_eps_cube : ((starRingEnd ℂ) airyEps) ^ 3 = -I := by
  rw [← map_pow, airyEps_cube, Complex.conj_I]

/-- `Ai(-q²) = -ω Ai((ε̄ q)²) - ω² Ai((ε q)²)`. -/
theorem airyAiC_neg_sq_rotation (q : ℂ) :
    airyAiC (-(q ^ 2)) = -(airyOmega * airyAiC (((starRingEnd ℂ) airyEps * q) ^ 2)) -
      airyOmega ^ 2 * airyAiC ((airyEps * q) ^ 2) := by
  have h := airyAiC_rotation (-(q ^ 2))
  have e1 : airyOmega * (-(q ^ 2)) = ((starRingEnd ℂ) airyEps * q) ^ 2 := by
    rw [mul_pow, airyConj_eps_sq]; ring
  have e2 : airyOmega ^ 2 * (-(q ^ 2)) = (airyEps * q) ^ 2 := by
    rw [mul_pow, airyEps_sq]; ring
  rw [e1, e2] at h
  linear_combination h

/-! ### The principal square roots `(π/(ε^{±1} q))^{1/2}` -/

lemma airyCos_pos_of_abs_le {φ : ℝ} (h : |φ| ≤ π / 4) : 0 < Real.cos φ := by
  have := abs_le.mp h
  exact Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩

lemma airyAbs_sin_le_cos {φ : ℝ} (h : |φ| ≤ π / 4) : |Real.sin φ| ≤ Real.cos φ := by
  have hc := airyCos_pos_of_abs_le h
  have h2 : 0 ≤ Real.cos (2 * φ) := by
    have := abs_le.mp h
    exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  rw [Real.cos_two_mul] at h2
  have := Real.sin_sq_add_cos_sq φ
  have h3 : |Real.sin φ| ^ 2 ≤ Real.cos φ ^ 2 := by rw [sq_abs]; nlinarith
  exact (pow_le_pow_iff_left₀ (abs_nonneg _) hc.le two_ne_zero).mp h3

/-- Rotating a complex number with `Re τ > 0`, `Re τ² > 0` by an angle `|φ| ≤ π/4` keeps `Re > 0`. -/
lemma airyRe_exp_mul_pos {τ : ℂ} (h0 : 0 < τ.re) (h2 : 0 < (τ ^ 2).re) {φ : ℝ} (hφ : |φ| ≤ π / 4) :
    0 < (cexp ((φ : ℂ) * I) * τ).re := by
  rw [Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  have hc := airyCos_pos_of_abs_le hφ
  have hs := airyAbs_sin_le_cos hφ
  rw [re_sq] at h2
  have hb : |τ.im| < τ.re := abs_lt_of_sq_lt_sq (by nlinarith) h0.le
  have h3 : Real.sin φ * τ.im ≤ |Real.sin φ| * |τ.im| := by
    rw [← abs_mul]; exact le_abs_self _
  have h4 : |Real.sin φ| * |τ.im| ≤ Real.cos φ * |τ.im| :=
    mul_le_mul_of_nonneg_right hs (abs_nonneg _)
  have h5 : Real.cos φ * |τ.im| < Real.cos φ * τ.re := mul_lt_mul_of_pos_left hb hc
  linarith

/-- `(π/(ρ q))^{1/2} = e^{-iφ} (π/q)^{1/2}` for `ρ = e^{2iφ}`, `|φ| ≤ π/4`, `Re q > 0`, `Re (ρ q) > 0`. -/
lemma airySqrt_pi_div_rot_mul {q ρ : ℂ} {φ : ℝ} (hq : 0 < q.re) (hφ : |φ| ≤ π / 4)
    (hρ : ρ = cexp (((2 * φ : ℝ) : ℂ) * I)) (hρq : 0 < (ρ * q).re) :
    ((π : ℂ) / (ρ * q)) ^ (1 / 2 : ℂ) = cexp (((-φ : ℝ) : ℂ) * I) * ((π : ℂ) / q) ^ (1 / 2 : ℂ) := by
  have hτ0 : 0 < (((π : ℂ) / q) ^ (1 / 2 : ℂ)).re := re_cpow_half_pos (re_div_pos hq)
  have hτ2 : 0 < ((((π : ℂ) / q) ^ (1 / 2 : ℂ)) ^ 2).re := by
    rw [cpow_half_sq]; exact re_div_pos hq
  have hq0 : q ≠ 0 := fun h => by simp [h] at hq
  have hρ0 : ρ ≠ 0 := by rw [hρ]; exact Complex.exp_ne_zero _
  symm
  apply eq_of_sq_eq_of_re_pos
  · rw [mul_pow, cpow_half_sq, cpow_half_sq, ← Complex.exp_nat_mul, hρ]
    have h1 : cexp (((2 : ℕ) : ℂ) * (((-φ : ℝ) : ℂ) * I)) = (cexp (((2 * φ : ℝ) : ℂ) * I))⁻¹ := by
      rw [← Complex.exp_neg]; congr 1; push_cast; ring
    rw [h1]
    have h2 : cexp (((2 * φ : ℝ) : ℂ) * I) ≠ 0 := Complex.exp_ne_zero _
    field_simp
  · exact airyRe_exp_mul_pos hτ0 hτ2 (by rw [abs_neg]; exact hφ)
  · exact re_cpow_half_pos (re_div_pos hρq)

/-! ### The leading terms and their cosine combination -/

lemma airyNeg_omega_mul_exp1 :
    -(airyOmega * cexp (((π / 12 : ℝ) : ℂ) * I)) = cexp (((-(π / 4) : ℝ) : ℂ) * I) := by
  rw [airyOmega_eq_exp', ← Complex.exp_add]
  have h1 : -cexp (((2 * π / 3 : ℝ) : ℂ) * I + ((π / 12 : ℝ) : ℂ) * I) =
      cexp (((2 * π / 3 : ℝ) : ℂ) * I + ((π / 12 : ℝ) : ℂ) * I + π * I) := by
    rw [Complex.exp_add _ ((π : ℂ) * I), Complex.exp_pi_mul_I]; ring
  rw [h1, Complex.exp_eq_exp_iff_exists_int]
  refine ⟨1, ?_⟩
  push_cast
  ring

lemma airyNeg_omega_sq_mul_exp2 :
    -(airyOmega ^ 2 * cexp (((-(π / 12) : ℝ) : ℂ) * I)) = cexp (((π / 4 : ℝ) : ℂ) * I) := by
  rw [airyOmega_sq_eq_exp, ← Complex.exp_add]
  have h1 : -cexp (((4 * π / 3 : ℝ) : ℂ) * I + ((-(π / 12) : ℝ) : ℂ) * I) =
      cexp (((4 * π / 3 : ℝ) : ℂ) * I + ((-(π / 12) : ℝ) : ℂ) * I + π * I) := by
    rw [Complex.exp_add _ ((π : ℂ) * I), Complex.exp_pi_mul_I]; ring
  rw [h1, Complex.exp_eq_exp_iff_exists_int]
  refine ⟨1, ?_⟩
  push_cast
  ring

/-- Leading term of `Ai((ε q)²)`. -/
lemma airyLead_eps_mul {q : ℂ} (hq : NegSector q) (hq0 : 0 < ‖q‖) :
    airyLead (airyEps * q) = (1 / (2 * (π : ℂ))) * cexp (-(I * ((2 / 3 : ℂ) * q ^ 3))) *
      (cexp (((-(π / 12) : ℝ) : ℂ) * I) * ((π : ℂ) / q) ^ (1 / 2 : ℂ)) := by
  have hre : 0 < q.re := lt_of_lt_of_le (by positivity) hq
  have hρ : airyEps = cexp (((2 * (π / 12) : ℝ) : ℂ) * I) := by
    rw [airyEps_eq_exp']; congr 2; push_cast; ring
  have hs := airySqrt_pi_div_rot_mul (q := q) (ρ := airyEps) (φ := π / 12) hre
    (by rw [abs_of_pos (by positivity)]; linarith [Real.pi_pos]) hρ
    (lt_of_lt_of_le (by positivity) hq.re_eps)
  unfold airyLead
  rw [hs, mul_pow, airyEps_cube]
  congr 3
  ring

/-- Leading term of `Ai((ε̄ q)²)`. -/
lemma airyLead_conj_eps_mul {q : ℂ} (hq : NegSector q) (hq0 : 0 < ‖q‖) :
    airyLead ((starRingEnd ℂ) airyEps * q) = (1 / (2 * (π : ℂ))) * cexp (I * ((2 / 3 : ℂ) * q ^ 3)) *
      (cexp (((π / 12 : ℝ) : ℂ) * I) * ((π : ℂ) / q) ^ (1 / 2 : ℂ)) := by
  have hre : 0 < q.re := lt_of_lt_of_le (by positivity) hq
  have hρ : (starRingEnd ℂ) airyEps = cexp (((2 * (-(π / 12)) : ℝ) : ℂ) * I) := by
    rw [conj_airyEps_eq_exp]; congr 2; push_cast; ring
  have hs := airySqrt_pi_div_rot_mul (q := q) (ρ := (starRingEnd ℂ) airyEps) (φ := -(π / 12)) hre
    (by rw [abs_neg, abs_of_pos (by positivity)]; linarith [Real.pi_pos]) hρ
    (lt_of_lt_of_le (by positivity) hq.re_conj_eps)
  unfold airyLead
  rw [hs, mul_pow, airyConj_eps_cube, neg_neg]
  congr 3
  ring

/-- The two leading terms combine to `(1/π) (π/q)^{1/2} cos(ξ - π/4)`, `ξ = (2/3) q³`. -/
lemma airyLead_sum_eq {q : ℂ} (hq : NegSector q) (hq0 : 0 < ‖q‖) :
    -(airyOmega * airyLead ((starRingEnd ℂ) airyEps * q)) - airyOmega ^ 2 * airyLead (airyEps * q) =
      (1 / (π : ℂ)) * ((π : ℂ) / q) ^ (1 / 2 : ℂ) * Complex.cos ((2 / 3 : ℂ) * q ^ 3 - (π / 4 : ℂ)) := by
  rw [airyLead_eps_mul hq hq0, airyLead_conj_eps_mul hq hq0]
  set τ := ((π : ℂ) / q) ^ (1 / 2 : ℂ)
  set ξ : ℂ := (2 / 3 : ℂ) * q ^ 3
  have h1 := airyNeg_omega_mul_exp1
  have h2 := airyNeg_omega_sq_mul_exp2
  have hc : 2 * Complex.cos (ξ - (π / 4 : ℂ)) =
      cexp (I * ξ) * cexp (((-(π / 4) : ℝ) : ℂ) * I) + cexp (-(I * ξ)) * cexp (((π / 4 : ℝ) : ℂ) * I) := by
    rw [Complex.two_cos, ← Complex.exp_add, ← Complex.exp_add]
    congr 2 <;> push_cast <;> ring
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  have hcos : Complex.cos (ξ - (π / 4 : ℂ)) = 1 / 2 *
      (cexp (I * ξ) * cexp (((-(π / 4) : ℝ) : ℂ) * I) + cexp (-(I * ξ)) * cexp (((π / 4 : ℝ) : ℂ) * I)) := by
    rw [← hc]; ring
  rw [hcos]
  linear_combination (1 / (2 * (π : ℂ)) * cexp (I * ξ) * τ) * h1 +
    (1 / (2 * (π : ℂ)) * cexp (-(I * ξ)) * τ) * h2

/-! ### The remainder -/

lemma airyNegc_const_le {N : ℝ} (hN : 0 < N) :
    5 / 48 / ((1 / 2 : ℝ) ^ 3 * √(1 / 2 : ℝ) * N ^ 3) ≤ 6 / 5 / N ^ 3 := by
  have h : (7 / 10 : ℝ) ≤ √(1 / 2 : ℝ) := by
    apply Real.le_sqrt_of_sq_le; norm_num
  have hpos : 0 < (1 / 2 : ℝ) ^ 3 * √(1 / 2 : ℝ) * N ^ 3 := by positivity
  rw [div_le_div_iff₀ hpos (by positivity)]
  have : (7 / 80 : ℝ) * N ^ 3 ≤ (1 / 2 : ℝ) ^ 3 * √(1 / 2 : ℝ) * N ^ 3 := by
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h (by norm_num : (0:ℝ) ≤ (1 / 2) ^ 3))
      (by positivity : (0:ℝ) ≤ N ^ 3)
    nlinarith
  nlinarith [pow_pos hN 3]

lemma airyNorm_cexp_le_of_re {w : ℂ} {Y : ℝ} (h : (-(2 / 3) * w ^ 3).re ≤ Y) :
    ‖cexp (-(2 / 3) * w ^ 3)‖ ≤ Real.exp Y := by
  rw [Complex.norm_exp]; exact Real.exp_le_exp.mpr h

lemma airyRe_phase_eps (q : ℂ) : (-(2 / 3) * (airyEps * q) ^ 3).re = ((2 / 3 : ℂ) * q ^ 3).im := by
  rw [mul_pow, airyEps_cube]
  simp [Complex.mul_re, Complex.mul_im]

lemma airyRe_phase_conj_eps (q : ℂ) :
    (-(2 / 3) * ((starRingEnd ℂ) airyEps * q) ^ 3).re = -((2 / 3 : ℂ) * q ^ 3).im := by
  rw [mul_pow, airyConj_eps_cube]
  simp [Complex.mul_re, Complex.mul_im]

/-- **`Ai` in a complex neighbourhood of the negative axis** (DLMF 9.7.9 with explicit remainder).
For `q ≠ 0` with `|arg q| ≤ π/6` (`NegSector`), `ξ = (2/3) q³`:
`‖Ai(-q²) - (1/π) (π/q)^{1/2} cos(ξ - π/4)‖ ≤ (6/5) e^{|Im ξ|} (√(π/‖q‖)/π) / ‖q‖³`. -/
theorem airyAiC_neg_complex {q : ℂ} (hq : NegSector q) (hq0 : 0 < ‖q‖) :
    ‖airyAiC (-(q ^ 2)) - (1 / (π : ℂ)) * ((π : ℂ) / q) ^ (1 / 2 : ℂ) *
        Complex.cos ((2 / 3 : ℂ) * q ^ 3 - (π / 4 : ℂ))‖ ≤
      6 / 5 * Real.exp |((2 / 3 : ℂ) * q ^ 3).im| * (√(π / ‖q‖) / π) / ‖q‖ ^ 3 := by
  set Y := |((2 / 3 : ℂ) * q ^ 3).im| with hY
  have hre : 0 < q.re := lt_of_lt_of_le (by positivity) hq
  have hw1 := hq.re_conj_eps
  have hw2 := hq.re_eps
  have e : airyAiC (-(q ^ 2)) - (1 / (π : ℂ)) * ((π : ℂ) / q) ^ (1 / 2 : ℂ) *
        Complex.cos ((2 / 3 : ℂ) * q ^ 3 - (π / 4 : ℂ)) =
      -(airyOmega * (airyAiC (((starRingEnd ℂ) airyEps * q) ^ 2) - airyLead ((starRingEnd ℂ) airyEps * q))) -
        airyOmega ^ 2 * (airyAiC ((airyEps * q) ^ 2) - airyLead (airyEps * q)) := by
    rw [← airyLead_sum_eq hq hq0, airyAiC_neg_sq_rotation]
    ring
  rw [e]
  have b1 := norm_airyAiC_sq_sub_lead_le (w := (starRingEnd ℂ) airyEps * q) (s := 1 / 2) (by norm_num)
    (by rw [airyNorm_conj_eps_mul]; linarith) (by linarith)
  have b2 := norm_airyAiC_sq_sub_lead_le (w := airyEps * q) (s := 1 / 2) (by norm_num)
    (by rw [airyNorm_eps_mul]; linarith) (by linarith)
  rw [airyNorm_conj_eps_mul] at b1
  rw [airyNorm_eps_mul] at b2
  have c := airyNegc_const_le hq0
  have n1 : ‖airyLead ((starRingEnd ℂ) airyEps * q)‖ ≤
      1 / (2 * π) * Real.exp Y * √(π / ‖q‖) := by
    rw [norm_airyLead, airyNorm_conj_eps_mul]
    have := airyNorm_cexp_le_of_re (w := (starRingEnd ℂ) airyEps * q) (Y := Y) (by
      rw [airyRe_phase_conj_eps]; exact (neg_le_abs _).trans (le_of_eq hY.symm))
    gcongr
  have n2 : ‖airyLead (airyEps * q)‖ ≤ 1 / (2 * π) * Real.exp Y * √(π / ‖q‖) := by
    rw [norm_airyLead, airyNorm_eps_mul]
    have := airyNorm_cexp_le_of_re (w := airyEps * q) (Y := Y) (by
      rw [airyRe_phase_eps]; exact (le_abs_self _).trans (le_of_eq hY.symm))
    gcongr
  have hω : ‖airyOmega‖ = 1 := norm_airyOmega
  have hω2 : ‖airyOmega ^ 2‖ = 1 := norm_airyOmega_sq
  have hN3 : 0 < ‖q‖ ^ 3 := by positivity
  calc ‖-(airyOmega * (airyAiC (((starRingEnd ℂ) airyEps * q) ^ 2) - airyLead ((starRingEnd ℂ) airyEps * q))) -
        airyOmega ^ 2 * (airyAiC ((airyEps * q) ^ 2) - airyLead (airyEps * q))‖
      ≤ ‖airyAiC (((starRingEnd ℂ) airyEps * q) ^ 2) - airyLead ((starRingEnd ℂ) airyEps * q)‖ +
        ‖airyAiC ((airyEps * q) ^ 2) - airyLead (airyEps * q)‖ := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_neg, norm_mul, norm_mul, hω, hω2, one_mul, one_mul]
    _ ≤ 6 / 5 / ‖q‖ ^ 3 * (1 / (2 * π) * Real.exp Y * √(π / ‖q‖)) +
        6 / 5 / ‖q‖ ^ 3 * (1 / (2 * π) * Real.exp Y * √(π / ‖q‖)) := by
        have hc : 0 ≤ 6 / 5 / ‖q‖ ^ 3 := by positivity
        refine add_le_add (b1.trans ?_) (b2.trans ?_)
        · exact (mul_le_mul_of_nonneg_right c (norm_nonneg _)).trans (mul_le_mul_of_nonneg_left n1 hc)
        · exact (mul_le_mul_of_nonneg_right c (norm_nonneg _)).trans (mul_le_mul_of_nonneg_left n2 hc)
    _ = _ := by field_simp; ring

/-- info: 'FormalResearch.Special.airyAiC_neg_complex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyAiC_neg_complex

end FormalResearch.Special
