module

public import FormalResearch.Special.AiryAsymSaddle
public import FormalResearch.Special.AiryEnvelopeSector

/-!
# `Ai`, `Ai'`, `Bi` on the negative axis with explicit error (no Olver theory)

From the saddle-point estimates of `AiryAsymSaddle` at `w = r e^{iπ/6}` (`r = √y`; then `w² = y e^{iπ/3}`,
`w³ = i r³`, so `|e^{-(2/3)w³}| = 1` and `ρ = Re w = (√3/2) r`) and the three-fold rotation identity
`Ai(-y) = -ω Ai(-ωy) - ω² Ai(-ω² y)` (with `-ω² y = y e^{iπ/3} = w²`, `-ω y = conj(w²)`), one obtains
for every `y > 0` (so for `ξ = (2/3) y^{3/2}`):

* `airyAi_neg_asymptotic`   `|Ai(-y) - π^{-1/2} y^{-1/4} cos(ξ - π/4)| ≤ (1/8) y^{-7/4}`,
* `airyAi'_neg_asymptotic`  `|Ai'(-y) - π^{-1/2} y^{1/4} sin(ξ - π/4)| ≤ (2/5) y^{-5/4}`,
* `airyBi_neg_asymptotic`   `|Bi(-y) + π^{-1/2} y^{-1/4} sin(ξ - π/4)| ≤ (1/8) y^{-7/4}`

(DLMF 9.7.9, 9.7.10, 9.7.11 with the first error term made explicit: relative error `O(y^{-3/2})`).
The constants `1/8`, `2/5` are those of the proof (true constants are smaller: numerically
`|err| · y^{7/4} ≤ 0.07`); the ranges are all `y > 0` (the estimate is only informative for large `y`).

Not formalised here: the full asymptotic series (`u_k` coefficients; only `u_1` is in `AiryAsymChi`), and
uniform-in-sector statements.  `Bi'` on the negative axis is `AiryAsymBiNeg`, `Bi`, `Bi'` on the positive axis
`AiryAsymBiPos`, and the `u_1` term of `Ai`, `Bi` on the negative axis is `AiryAsymChi`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.Special

private lemma sqrt3_mul' : √(3 : ℝ) * √3 = 3 := Real.mul_self_sqrt (by norm_num)

private lemma sqrt3_cube' : √(3 : ℝ) * √3 * √3 = 3 * √3 := by rw [sqrt3_mul']

/-! ### Algebra of `ε = e^{iπ/6}` and `ω = e^{2πi/3}` -/

lemma airyEps_sq : airyEps ^ 2 = -(airyOmega ^ 2) := by
  apply Complex.ext <;> simp [airyEps, airyOmega, pow_succ, Complex.mul_re, Complex.mul_im] <;>
    nlinarith [sqrt3_mul']

lemma airyEps_cube : airyEps ^ 3 = I := by
  apply Complex.ext <;> simp [airyEps, pow_succ, Complex.mul_re, Complex.mul_im] <;>
    nlinarith [sqrt3_mul', sqrt3_cube']

lemma norm_airyEps : ‖airyEps‖ = 1 := by
  rw [airyEps_eq_exp, Complex.norm_exp]
  simp

lemma airyOmega_sq_eq_exp : airyOmega ^ 2 = cexp (((4 * π / 3 : ℝ) : ℂ) * I) := by
  rw [airyOmega_eq_exp, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma airyOmega_eq_exp' : airyOmega = cexp (((2 * π / 3 : ℝ) : ℂ) * I) := by
  rw [airyOmega_eq_exp]
  congr 1
  push_cast
  ring

lemma airyEps_eq_exp' : airyEps = cexp (((π / 6 : ℝ) : ℂ) * I) := by
  rw [airyEps_eq_exp]
  congr 1
  push_cast
  ring

lemma conj_airyEps_eq_exp : (starRingEnd ℂ) airyEps = cexp (((-(π / 6) : ℝ) : ℂ) * I) := by
  rw [airyEps_eq_exp', ← Complex.exp_conj]
  congr 1
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- The rotated saddle `w = r e^{iπ/6}` (so that `w² = -ω² r²`). -/
noncomputable def negW (r : ℝ) : ℂ := (r : ℂ) * airyEps

lemma re_negW (r : ℝ) : (negW r).re = r * (√3 / 2) := by simp [negW, airyEps]

lemma negW_sq (r : ℝ) : negW r ^ 2 = airyOmega ^ 2 * ((-(r ^ 2) : ℝ) : ℂ) := by
  unfold negW
  rw [mul_pow, airyEps_sq]
  push_cast
  ring

lemma conj_negW_sq (r : ℝ) : (starRingEnd ℂ) (negW r ^ 2) = airyOmega * ((-(r ^ 2) : ℝ) : ℂ) := by
  rw [negW_sq, map_mul, conj_airyOmega_sq, Complex.conj_ofReal]

lemma negW_cube (r : ℝ) : negW r ^ 3 = (r : ℂ) ^ 3 * I := by
  unfold negW
  rw [mul_pow, airyEps_cube]

lemma exp_negW_cube (r : ℝ) :
    cexp (-(2 / 3) * negW r ^ 3) = cexp (((-(2 / 3 * r ^ 3) : ℝ) : ℂ) * I) := by
  rw [negW_cube]
  congr 1
  push_cast
  ring

lemma norm_exp_negW_cube (r : ℝ) : ‖cexp (-(2 / 3) * negW r ^ 3)‖ = 1 := by
  rw [exp_negW_cube]
  exact Complex.norm_exp_ofReal_mul_I _

lemma norm_negW (r : ℝ) (hr : 0 < r) : ‖negW r‖ = r := by
  unfold negW
  rw [norm_mul, norm_airyEps, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, mul_one]

/-! ### The principal square root `(π/w)^{1/2}` at `w = r e^{iπ/6}` -/

lemma eq_of_sq_eq_of_re_pos {a b : ℂ} (h : a ^ 2 = b ^ 2) (ha : 0 < a.re) (hb : 0 < b.re) : a = b := by
  have h1 : (a - b) * (a + b) = 0 := by linear_combination h
  have h2 : a + b ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    rw [Complex.add_re, Complex.zero_re] at this
    linarith
  exact sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_right h2)

lemma re_cpow_half_pos {x : ℂ} (hx : 0 < x.re) : 0 < (x ^ (1 / 2 : ℂ)).re := by
  have hx0 : x ≠ 0 := fun h => by simp [h] at hx
  rw [Complex.cpow_def_of_ne_zero hx0, Complex.exp_re]
  refine mul_pos (Real.exp_pos _) ?_
  have harg : |x.arg| < π / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hx)
  have : (Complex.log x * (1 / 2 : ℂ)).im = x.arg / 2 := by
    simp [Complex.log_im]
    ring
  rw [this]
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> linarith [abs_lt.mp harg]

lemma re_div_pos {w : ℂ} (hw : 0 < w.re) : 0 < ((π : ℂ) / w).re := by
  have : ((π : ℂ) / w).re = π * w.re / Complex.normSq w := by
    rw [Complex.div_re]; simp [Complex.normSq_apply]
  rw [this]
  have : 0 < Complex.normSq w := Complex.normSq_pos.mpr (fun h => by simp [h] at hw)
  positivity

lemma sqrt_pi_div_negW {r : ℝ} (hr : 0 < r) :
    ((π : ℂ) / negW r) ^ (1 / 2 : ℂ) =
      ((√(π / r) : ℝ) : ℂ) * cexp (((-(π / 12) : ℝ) : ℂ) * I) := by
  have hw : 0 < (negW r).re := by rw [re_negW]; positivity
  have hb2 : (((√(π / r) : ℝ) : ℂ) * cexp (((-(π / 12) : ℝ) : ℂ) * I)) ^ 2 = π / negW r := by
    unfold negW
    rw [airyEps_eq_exp', mul_pow, ← Complex.exp_nat_mul, ← Complex.ofReal_pow,
      Real.sq_sqrt (by positivity)]
    have : cexp (((2 : ℕ) : ℂ) * (((-(π / 12) : ℝ) : ℂ) * I)) =
        (cexp (((π / 6 : ℝ) : ℂ) * I))⁻¹ := by
      rw [← Complex.exp_neg]; congr 1; push_cast; ring
    rw [this]
    push_cast
    have : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    field_simp
  have hbre : 0 < (((√(π / r) : ℝ) : ℂ) * cexp (((-(π / 12) : ℝ) : ℂ) * I)).re := by
    rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
    refine mul_pos (Real.sqrt_pos.mpr (by positivity)) (Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩)
    · linarith [Real.pi_pos]
    · linarith [Real.pi_pos]
  apply eq_of_sq_eq_of_re_pos
  · rw [hb2]
    simp
  · exact re_cpow_half_pos (re_div_pos hw)
  · exact hbre

/-! ### The leading terms -/

lemma exp_add_ofReal_mul_I (a b : ℝ) :
    cexp (((a + b : ℝ) : ℂ) * I) = cexp ((a : ℂ) * I) * cexp ((b : ℂ) * I) := by
  rw [← Complex.exp_add]; congr 1; push_cast; ring

lemma re_exp_mul_exp (c a θ : ℝ) :
    (cexp ((a : ℂ) * I) * ((c : ℂ) * cexp ((θ : ℂ) * I))).re = c * Real.cos (a + θ) := by
  have : cexp ((a : ℂ) * I) * ((c : ℂ) * cexp ((θ : ℂ) * I)) =
      (c : ℂ) * cexp (((a + θ : ℝ) : ℂ) * I) := by
    rw [exp_add_ofReal_mul_I]; ring
  rw [this, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

/-- The leading term of `Ai(w²)` at `w = r e^{iπ/6}`: modulus `(1/2π)√(π/r)`, phase `-(2/3)r³ - π/12`. -/
lemma lead_Ai {r : ℝ} (hr : 0 < r) :
    (1 / (2 * (π : ℂ))) * cexp (-(2 / 3) * negW r ^ 3) * (π / negW r) ^ (1 / 2 : ℂ) =
      ((1 / (2 * π) * √(π / r) : ℝ) : ℂ) * cexp (((-(2 / 3 * r ^ 3) - π / 12 : ℝ) : ℂ) * I) := by
  rw [exp_negW_cube, sqrt_pi_div_negW hr, show (-(2 / 3 * r ^ 3) - π / 12 : ℝ) =
    -(2 / 3 * r ^ 3) + (-(π / 12)) by ring, exp_add_ofReal_mul_I]
  push_cast
  ring

/-- The leading term `(1/2π) e^{-(2/3)w³} w (π/w)^{1/2}` of `-Ai'(w²)`. -/
lemma lead_Ai' {r : ℝ} (hr : 0 < r) :
    (1 / (2 * (π : ℂ))) * cexp (-(2 / 3) * negW r ^ 3) * (negW r * (π / negW r) ^ (1 / 2 : ℂ)) =
      ((1 / (2 * π) * √(π / r) * r : ℝ) : ℂ) * cexp (((-(2 / 3 * r ^ 3) + π / 12 : ℝ) : ℂ) * I) := by
  rw [exp_negW_cube, sqrt_pi_div_negW hr, show (-(2 / 3 * r ^ 3) + π / 12 : ℝ) =
    -(2 / 3 * r ^ 3) + (π / 6 + (-(π / 12))) by ring, exp_add_ofReal_mul_I, exp_add_ofReal_mul_I]
  unfold negW
  rw [airyEps_eq_exp']
  push_cast
  ring

/-! ### Rotation identities -/

/-- Derivative of the three-fold rotation identity. -/
theorem deriv_airyAiC_rotation (z : ℂ) :
    deriv airyAiC z + airyOmega ^ 2 * deriv airyAiC (airyOmega * z) +
      airyOmega * deriv airyAiC (airyOmega ^ 2 * z) = 0 := by
  have hω3 := airyOmega_cube
  have hω4 : airyOmega ^ 2 * airyOmega ^ 2 = airyOmega := by
    rw [← pow_add, show 2 + 2 = 3 + 1 by norm_num, pow_add, hω3, one_mul, pow_one]
  have h1 : HasDerivAt (fun z : ℂ => airyOmega * z) airyOmega z := by
    simpa using (hasDerivAt_id z).const_mul airyOmega
  have h2 : HasDerivAt (fun z : ℂ => airyOmega ^ 2 * z) (airyOmega ^ 2) z := by
    simpa using (hasDerivAt_id z).const_mul (airyOmega ^ 2)
  have hA : ∀ u : ℂ, HasDerivAt airyAiC (deriv airyAiC u) u := fun u =>
    (differentiable_airyAiC u).hasDerivAt
  have hf : HasDerivAt (fun z : ℂ => airyAiC z + airyOmega * airyAiC (airyOmega * z) +
      airyOmega ^ 2 * airyAiC (airyOmega ^ 2 * z))
      (deriv airyAiC z + airyOmega * (deriv airyAiC (airyOmega * z) * airyOmega) +
        airyOmega ^ 2 * (deriv airyAiC (airyOmega ^ 2 * z) * airyOmega ^ 2)) z :=
    ((hA z).add (((hA (airyOmega * z)).comp z h1).const_mul airyOmega)).add
      (((hA (airyOmega ^ 2 * z)).comp z h2).const_mul (airyOmega ^ 2))
  have h0 : (fun z : ℂ => airyAiC z + airyOmega * airyAiC (airyOmega * z) +
      airyOmega ^ 2 * airyAiC (airyOmega ^ 2 * z)) = fun _ => 0 := funext airyAiC_rotation
  rw [h0] at hf
  have := hf.unique (hasDerivAt_const z (0 : ℂ))
  linear_combination this - (deriv airyAiC (airyOmega ^ 2 * z)) * hω4

lemma conj_deriv_airyAiC (u : ℂ) :
    (starRingEnd ℂ) (deriv airyAiC u) = deriv airyAiC ((starRingEnd ℂ) u) := by
  rw [deriv_airyAiC one_pos, deriv_airyAiC one_pos]
  exact conj_airyMom 1 1 u

lemma re_conj_pair (a u : ℂ) : ((starRingEnd ℂ) a * (starRingEnd ℂ) u + a * u).re = 2 * (a * u).re := by
  rw [← map_mul, Complex.add_re, Complex.conj_re]
  ring

lemma abs_two_re_sub_le {a : ℂ} (ha : ‖a‖ = 1) (A L : ℂ) :
    |((starRingEnd ℂ) a * (starRingEnd ℂ) A + a * A).re - 2 * (a * L).re| ≤ 2 * ‖A - L‖ := by
  have e : 2 * (a * A).re - 2 * (a * L).re = 2 * (a * (A - L)).re := by
    rw [mul_sub, Complex.sub_re]; ring
  rw [re_conj_pair, e, abs_mul, abs_two]
  gcongr
  calc |(a * (A - L)).re| ≤ ‖a * (A - L)‖ := Complex.abs_re_le_norm _
    _ = ‖A - L‖ := by rw [norm_mul, ha, one_mul]

lemma airyAi_neg_eq (r : ℝ) :
    airyAi (-(r ^ 2)) = -((((starRingEnd ℂ) (airyOmega ^ 2)) *
      (starRingEnd ℂ) (airyAiC (negW r ^ 2)) + airyOmega ^ 2 * airyAiC (negW r ^ 2)).re) := by
  have h := airyAiC_rotation ((-(r ^ 2) : ℝ) : ℂ)
  have e1 : airyAiC (airyOmega * ((-(r ^ 2) : ℝ) : ℂ)) = (starRingEnd ℂ) (airyAiC (negW r ^ 2)) := by
    rw [← conj_negW_sq, conj_airyAiC]
  have e2 : airyAiC (airyOmega ^ 2 * ((-(r ^ 2) : ℝ) : ℂ)) = airyAiC (negW r ^ 2) := by
    rw [negW_sq]
  rw [e1, e2] at h
  have : airyAiC ((-(r ^ 2) : ℝ) : ℂ) = -((starRingEnd ℂ) (airyOmega ^ 2) *
      (starRingEnd ℂ) (airyAiC (negW r ^ 2)) + airyOmega ^ 2 * airyAiC (negW r ^ 2)) := by
    rw [conj_airyOmega_sq]
    linear_combination h
  unfold airyAi
  rw [this, Complex.neg_re]

lemma airyBi_neg_eq (r : ℝ) :
    airyBi (-(r ^ 2)) = (((starRingEnd ℂ) ((starRingEnd ℂ) airyEps) *
      (starRingEnd ℂ) (airyAiC (negW r ^ 2)) +
        (starRingEnd ℂ) airyEps * airyAiC (negW r ^ 2)).re) := by
  have e1 : airyAiC (airyOmega * ((-(r ^ 2) : ℝ) : ℂ)) = (starRingEnd ℂ) (airyAiC (negW r ^ 2)) := by
    rw [← conj_negW_sq, conj_airyAiC]
  have e2 : airyAiC (airyOmega ^ 2 * ((-(r ^ 2) : ℝ) : ℂ)) = airyAiC (negW r ^ 2) := by
    rw [negW_sq]
  unfold airyBi airyBiC
  rw [e1, e2, Complex.conj_conj]

lemma airyAi'_neg_eq (r : ℝ) :
    airyAi' (-(r ^ 2)) = -((((starRingEnd ℂ) airyOmega) *
      (starRingEnd ℂ) (deriv airyAiC (negW r ^ 2)) + airyOmega * deriv airyAiC (negW r ^ 2)).re) := by
  have h := deriv_airyAiC_rotation ((-(r ^ 2) : ℝ) : ℂ)
  have e1 : deriv airyAiC (airyOmega * ((-(r ^ 2) : ℝ) : ℂ)) =
      (starRingEnd ℂ) (deriv airyAiC (negW r ^ 2)) := by
    rw [← conj_negW_sq, conj_deriv_airyAiC]
  have e2 : deriv airyAiC (airyOmega ^ 2 * ((-(r ^ 2) : ℝ) : ℂ)) = deriv airyAiC (negW r ^ 2) := by
    rw [negW_sq]
  rw [e1, e2] at h
  have : deriv airyAiC ((-(r ^ 2) : ℝ) : ℂ) = -((starRingEnd ℂ) airyOmega *
      (starRingEnd ℂ) (deriv airyAiC (negW r ^ 2)) + airyOmega * deriv airyAiC (negW r ^ 2)) := by
    rw [conj_airyOmega]
    linear_combination h
  unfold airyAi'
  rw [this, Complex.neg_re]

lemma norm_conj_airyEps : ‖(starRingEnd ℂ) airyEps‖ = 1 := by
  rw [conj_airyEps_eq_exp]; exact Complex.norm_exp_ofReal_mul_I _

/-! ### Numerical bounds on the error terms -/

lemma sqrt_div_pow_le {r ρ : ℝ} (hr : 0 < r) (hρ : 5 / 6 * r ≤ ρ) (k : ℕ) :
    √(π / ρ) / ρ ^ k ≤ 10 / 9 * (6 / 5) ^ k * √π / (√r * r ^ k) := by
  have hρ0 : 0 < ρ := by linarith
  have hs : 0 < √r := Real.sqrt_pos.mpr hr
  have h1 : 9 / 10 * √r ≤ √ρ := by
    rw [Real.le_sqrt' (by positivity)]
    nlinarith [Real.sq_sqrt hr.le]
  have h2 : (5 / 6) ^ k * r ^ k ≤ ρ ^ k := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hρ k
  rw [Real.sqrt_div Real.pi_pos.le, div_div]
  have hπ : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
  calc √π / (√ρ * ρ ^ k) ≤ √π / (9 / 10 * √r * ((5 / 6) ^ k * r ^ k)) := by
        apply div_le_div_of_nonneg_left hπ.le (by positivity)
        exact mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = 10 / 9 * (6 / 5) ^ k * √π / (√r * r ^ k) := by
        simp only [div_pow]
        field_simp

lemma sqrtpi_ge : (8 / 5 : ℝ) ≤ √π := by
  rw [Real.le_sqrt' (by norm_num)]
  nlinarith [Real.pi_gt_three]

lemma errAi_le {r ρ : ℝ} (hr : 0 < r) (hρ : 5 / 6 * r ≤ ρ) :
    1 / (2 * π) * (5 / 48 * (√(π / ρ) / ρ ^ 3)) ≤ 1 / (16 * (√r * r ^ 3)) := by
  have h3 := sqrt_div_pow_le hr hρ 3
  have hs : 0 < √r := Real.sqrt_pos.mpr hr
  have hm : 0 < √r * r ^ 3 := by positivity
  have hT := sqrtpi_ge
  have hπ : √π * √π = π := Real.mul_self_sqrt Real.pi_pos.le
  calc 1 / (2 * π) * (5 / 48 * (√(π / ρ) / ρ ^ 3))
      ≤ 1 / (2 * π) * (5 / 48 * (10 / 9 * (6 / 5) ^ 3 * √π / (√r * r ^ 3))) := by gcongr
    _ = 1 / (10 * √π) * (1 / (√r * r ^ 3)) := by
        have hT0 : 0 < √π := by linarith
        generalize √π = T at hπ hT0
        rw [← hπ]
        field_simp
        ring
    _ ≤ 1 / 16 * (1 / (√r * r ^ 3)) := by
        gcongr
        linarith
    _ = 1 / (16 * (√r * r ^ 3)) := by field_simp

lemma errAi'_le {r ρ : ℝ} (hr : 0 < r) (hρ : 5 / 6 * r ≤ ρ) :
    1 / (2 * π) * (r * (5 / 48 * (√(π / ρ) / ρ ^ 3)) + 1 / 4 * (√(π / ρ) / ρ ^ 2)) ≤
      1 / (5 * (√r * r ^ 2)) := by
  have h3 := sqrt_div_pow_le hr hρ 3
  have h2 := sqrt_div_pow_le hr hρ 2
  have hs : 0 < √r := Real.sqrt_pos.mpr hr
  have hm : 0 < √r * r ^ 2 := by positivity
  have hT := sqrtpi_ge
  have hπ : √π * √π = π := Real.mul_self_sqrt Real.pi_pos.le
  calc 1 / (2 * π) * (r * (5 / 48 * (√(π / ρ) / ρ ^ 3)) + 1 / 4 * (√(π / ρ) / ρ ^ 2))
      ≤ 1 / (2 * π) * (r * (5 / 48 * (10 / 9 * (6 / 5) ^ 3 * √π / (√r * r ^ 3))) +
          1 / 4 * (10 / 9 * (6 / 5) ^ 2 * √π / (√r * r ^ 2))) := by gcongr
    _ = 3 / (10 * √π) * (1 / (√r * r ^ 2)) := by
        have hT0 : 0 < √π := by linarith
        generalize √π = T at hπ hT0
        rw [← hπ]
        field_simp
        ring
    _ ≤ 1 / 5 * (1 / (√r * r ^ 2)) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        rw [div_le_iff₀ (by positivity)]
        linarith
    _ = 1 / (5 * (√r * r ^ 2)) := by field_simp

lemma five_six_le_re_negW (r : ℝ) (hr : 0 < r) : 5 / 6 * r ≤ (negW r).re := by
  rw [re_negW]
  have : (5 / 3 : ℝ) ≤ √3 := by
    rw [Real.le_sqrt' (by norm_num)]; norm_num
  nlinarith

lemma norm_airyAiC_negW_sub_le {r : ℝ} (hr : 0 < r) :
    ‖airyAiC (negW r ^ 2) - ((1 / (2 * π) * √(π / r) : ℝ) : ℂ) *
        cexp (((-(2 / 3 * r ^ 3) - π / 12 : ℝ) : ℂ) * I)‖ ≤ 1 / (16 * (√r * r ^ 3)) := by
  have hw : 0 < (negW r).re := by rw [re_negW]; positivity
  have h := norm_airyAiC_sq_sub_le hw
  rw [lead_Ai hr, norm_exp_negW_cube, mul_one] at h
  exact h.trans (errAi_le hr (five_six_le_re_negW r hr))

lemma norm_deriv_airyAiC_negW_add_le {r : ℝ} (hr : 0 < r) :
    ‖deriv airyAiC (negW r ^ 2) + ((1 / (2 * π) * √(π / r) * r : ℝ) : ℂ) *
        cexp (((-(2 / 3 * r ^ 3) + π / 12 : ℝ) : ℂ) * I)‖ ≤ 1 / (5 * (√r * r ^ 2)) := by
  have hw : 0 < (negW r).re := by rw [re_negW]; positivity
  have h := norm_deriv_airyAiC_sq_add_le hw
  rw [lead_Ai' hr, norm_exp_negW_cube, mul_one, norm_negW r hr] at h
  exact h.trans (errAi'_le hr (five_six_le_re_negW r hr))

lemma lead_real_Ai {r : ℝ} (hr : 0 < r) :
    -2 * (1 / (2 * π) * √(π / r) * Real.cos (4 * π / 3 + (-(2 / 3 * r ^ 3) - π / 12))) =
      Real.cos (2 / 3 * r ^ 3 - π / 4) / (√π * √r) := by
  have e : Real.cos (4 * π / 3 + (-(2 / 3 * r ^ 3) - π / 12)) = -Real.cos (2 / 3 * r ^ 3 - π / 4) := by
    rw [show 4 * π / 3 + (-(2 / 3 * r ^ 3) - π / 12) = (π / 4 - 2 / 3 * r ^ 3) + π by ring,
      Real.cos_add_pi, show π / 4 - 2 / 3 * r ^ 3 = -(2 / 3 * r ^ 3 - π / 4) by ring, Real.cos_neg]
  rw [e, Real.sqrt_div Real.pi_pos.le]
  have hπ : √π * √π = π := Real.mul_self_sqrt Real.pi_pos.le
  have hs : 0 < √r := Real.sqrt_pos.mpr hr
  have hT : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
  generalize √π = T at hπ hT
  rw [← hπ]
  field_simp

lemma lead_real_Bi {r : ℝ} (hr : 0 < r) :
    2 * (1 / (2 * π) * √(π / r) * Real.cos (-(π / 6) + (-(2 / 3 * r ^ 3) - π / 12))) =
      -Real.sin (2 / 3 * r ^ 3 - π / 4) / (√π * √r) := by
  have e : Real.cos (-(π / 6) + (-(2 / 3 * r ^ 3) - π / 12)) = -Real.sin (2 / 3 * r ^ 3 - π / 4) := by
    rw [show -(π / 6) + (-(2 / 3 * r ^ 3) - π / 12) = -((2 / 3 * r ^ 3 - π / 4) + π / 2) by ring,
      Real.cos_neg, Real.cos_add_pi_div_two]
  rw [e, Real.sqrt_div Real.pi_pos.le]
  have hπ : √π * √π = π := Real.mul_self_sqrt Real.pi_pos.le
  have hs : 0 < √r := Real.sqrt_pos.mpr hr
  have hT : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
  generalize √π = T at hπ hT
  rw [← hπ]
  field_simp

lemma lead_real_Ai' {r : ℝ} (hr : 0 < r) :
    2 * (1 / (2 * π) * √(π / r) * r * Real.cos (2 * π / 3 + (-(2 / 3 * r ^ 3) + π / 12))) =
      √r * Real.sin (2 / 3 * r ^ 3 - π / 4) / √π := by
  have e : Real.cos (2 * π / 3 + (-(2 / 3 * r ^ 3) + π / 12)) = Real.sin (2 / 3 * r ^ 3 - π / 4) := by
    rw [show 2 * π / 3 + (-(2 / 3 * r ^ 3) + π / 12) = -((2 / 3 * r ^ 3 - π / 4) - π / 2) by ring,
      Real.cos_neg, Real.cos_sub_pi_div_two]
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

/-- **`Ai` on the negative axis**, in the variable `r = √y`: for `r > 0`,
`|Ai(-r²) - cos((2/3) r³ - π/4)/(√π √r)| ≤ 1/(8 √r r³)`. -/
theorem airyAi_neg_sq_asymptotic {r : ℝ} (hr : 0 < r) :
    |airyAi (-(r ^ 2)) - Real.cos (2 / 3 * r ^ 3 - π / 4) / (√π * √r)| ≤ 1 / (8 * (√r * r ^ 3)) := by
  set A := airyAiC (negW r ^ 2) with hA
  set L : ℂ := ((1 / (2 * π) * √(π / r) : ℝ) : ℂ) *
    cexp (((-(2 / 3 * r ^ 3) - π / 12 : ℝ) : ℂ) * I) with hL
  have h1 := abs_two_re_sub_le norm_airyOmega_sq A L
  have h2 : (airyOmega ^ 2 * L).re =
      1 / (2 * π) * √(π / r) * Real.cos (4 * π / 3 + (-(2 / 3 * r ^ 3) - π / 12)) := by
    rw [hL, airyOmega_sq_eq_exp]; exact re_exp_mul_exp _ _ _
  have h3 : airyAi (-(r ^ 2)) - Real.cos (2 / 3 * r ^ 3 - π / 4) / (√π * √r) =
      -(((starRingEnd ℂ) (airyOmega ^ 2) * (starRingEnd ℂ) A + airyOmega ^ 2 * A).re -
        2 * (airyOmega ^ 2 * L).re) := by
    rw [airyAi_neg_eq, ← lead_real_Ai hr, h2]; ring
  rw [h3, abs_neg]
  have h4 := norm_airyAiC_negW_sub_le hr
  calc _ ≤ 2 * ‖A - L‖ := h1
    _ ≤ 2 * (1 / (16 * (√r * r ^ 3))) := by gcongr
    _ = 1 / (8 * (√r * r ^ 3)) := by
        have : 0 < √r := Real.sqrt_pos.mpr hr
        field_simp; ring

/-- **`Bi` on the negative axis**, in the variable `r = √y`: for `r > 0`,
`|Bi(-r²) + sin((2/3) r³ - π/4)/(√π √r)| ≤ 1/(8 √r r³)`. -/
theorem airyBi_neg_sq_asymptotic {r : ℝ} (hr : 0 < r) :
    |airyBi (-(r ^ 2)) + Real.sin (2 / 3 * r ^ 3 - π / 4) / (√π * √r)| ≤ 1 / (8 * (√r * r ^ 3)) := by
  set A := airyAiC (negW r ^ 2) with hA
  set L : ℂ := ((1 / (2 * π) * √(π / r) : ℝ) : ℂ) *
    cexp (((-(2 / 3 * r ^ 3) - π / 12 : ℝ) : ℂ) * I) with hL
  have h1 := abs_two_re_sub_le norm_conj_airyEps A L
  have h2 : ((starRingEnd ℂ) airyEps * L).re =
      1 / (2 * π) * √(π / r) * Real.cos (-(π / 6) + (-(2 / 3 * r ^ 3) - π / 12)) := by
    rw [hL, conj_airyEps_eq_exp]; exact re_exp_mul_exp _ _ _
  have h3 : airyBi (-(r ^ 2)) + Real.sin (2 / 3 * r ^ 3 - π / 4) / (√π * √r) =
      (((starRingEnd ℂ) ((starRingEnd ℂ) airyEps) * (starRingEnd ℂ) A +
        (starRingEnd ℂ) airyEps * A).re - 2 * ((starRingEnd ℂ) airyEps * L).re) := by
    have := lead_real_Bi hr
    rw [airyBi_neg_eq, h2]
    have h5 : Real.sin (2 / 3 * r ^ 3 - π / 4) / (√π * √r) =
        -(2 * (1 / (2 * π) * √(π / r) * Real.cos (-(π / 6) + (-(2 / 3 * r ^ 3) - π / 12)))) := by
      rw [this]; ring
    rw [h5]; ring
  rw [h3]
  have h4 := norm_airyAiC_negW_sub_le hr
  calc _ ≤ 2 * ‖A - L‖ := h1
    _ ≤ 2 * (1 / (16 * (√r * r ^ 3))) := by gcongr
    _ = 1 / (8 * (√r * r ^ 3)) := by
        have : 0 < √r := Real.sqrt_pos.mpr hr
        field_simp; ring

/-- **`Ai'` on the negative axis**, in the variable `r = √y`: for `r > 0`,
`|Ai'(-r²) - √r sin((2/3) r³ - π/4)/√π| ≤ 2/(5 √r r²)`. -/
theorem airyAi'_neg_sq_asymptotic {r : ℝ} (hr : 0 < r) :
    |airyAi' (-(r ^ 2)) - √r * Real.sin (2 / 3 * r ^ 3 - π / 4) / √π| ≤ 2 / (5 * (√r * r ^ 2)) := by
  set A := deriv airyAiC (negW r ^ 2) with hA
  set L : ℂ := -(((1 / (2 * π) * √(π / r) * r : ℝ) : ℂ) *
    cexp (((-(2 / 3 * r ^ 3) + π / 12 : ℝ) : ℂ) * I)) with hL
  have h1 := abs_two_re_sub_le norm_airyOmega A L
  have h2 : (airyOmega * L).re =
      -(1 / (2 * π) * √(π / r) * r * Real.cos (2 * π / 3 + (-(2 / 3 * r ^ 3) + π / 12))) := by
    rw [hL, mul_neg, Complex.neg_re, airyOmega_eq_exp']
    rw [re_exp_mul_exp]
  have h3 : airyAi' (-(r ^ 2)) - √r * Real.sin (2 / 3 * r ^ 3 - π / 4) / √π =
      -(((starRingEnd ℂ) airyOmega * (starRingEnd ℂ) A + airyOmega * A).re -
        2 * (airyOmega * L).re) := by
    have := lead_real_Ai' hr
    rw [airyAi'_neg_eq, h2, ← this]; ring
  rw [h3, abs_neg]
  have h4 : ‖A - L‖ ≤ 1 / (5 * (√r * r ^ 2)) := by
    have := norm_deriv_airyAiC_negW_add_le hr
    rw [hL, sub_neg_eq_add]
    exact this
  calc _ ≤ 2 * ‖A - L‖ := h1
    _ ≤ 2 * (1 / (5 * (√r * r ^ 2))) := by gcongr
    _ = 2 / (5 * (√r * r ^ 2)) := by ring

/-- info: 'FormalResearch.Special.airyAi_neg_sq_asymptotic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyAi_neg_sq_asymptotic

/-- info: 'FormalResearch.Special.airyAi'_neg_sq_asymptotic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyAi'_neg_sq_asymptotic

/-- info: 'FormalResearch.Special.airyBi_neg_sq_asymptotic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyBi_neg_sq_asymptotic

end FormalResearch.Special
