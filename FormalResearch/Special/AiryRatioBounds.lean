module

public import FormalResearch.Special.AiryGoodCircles

/-!
# The Hermite-Biehler ratios `R_± = (Bi ∓ iAi)/Ai` on good circles

Input to the residue/defect formula (CFT/PR240 `AIRY_POISSON.md` §0, Theorem D): with `ω = e^{2πi/3}`,
`ε = e^{iπ/6}` and the definition `Bi(z) = ε Ai(ωz) + ε̄ Ai(ω²z)`, the rotation identity gives the connection
formulas (DLMF 9.2.10)

* `airyBiC_sub_I_mul_airyAiC` : `Bi(z) - i Ai(z) = 2 ε̄ Ai(ω² z)`   (`= -2i e^{iπ/3} Ai(ω̄ z)`),
* `airyBiC_add_I_mul_airyAiC` : `Bi(z) + i Ai(z) = 2 ε Ai(ω z)`.

For `Im u ≥ 0` the principal root of `ω² u` is `e^{-iπ/3} u^{1/2}`, hence `(ω² u)^{3/2} = -u^{3/2}`
(`re_cpow_three_halves_omega_sq`).  With (E1) for the numerator and the good-circle bound
(`AiryGoodCircles`) for the denominator:

* `airy_Rplus_bound` : on a good circle, for `Im u ≥ 0`:
  `‖(Bi(u) - i Ai(u))/Ai(u)‖ · e(u) ≤ 30 √π`;  `airy_Rminus_bound`: the same for `Im u ≤ 0` and `(Bi + iAi)/Ai`.

The constant `30√π ≈ 53` is far from the numerical `C_0 ≈ 2.01` of the notes (it is the product of the (E1)
constant `3`, the good-circle constant `1/(25π)` and a factor `2`).  Numerical check (mpmath, 80 digits): the connection
formulas hold to `1e-77`; `2‖Ai(ω²u)/Ai(u)‖ e(u)` on the circles `r_k`, `k ∈ {10,11,15,20,40,100}` (upper half circle,
361 angles) has supremum `2.012` (attained on the positive axis, tends to `2`), as in the notes.  The defect formula
itself (`Ai` zeros as simple poles, Cauchy on the two half discs, `Bi(a_n) = -1/(π Ai'(a_n))`) is not in this file but
in `AiryCftDefect` (`airy_defect_bound`, for entire `f`); `AiryCftQuadrature` combines it with the bounds here.  Not formalised: the
`P·Ai + Q·Ai'` versions.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.Special

/-! ### Connection formulas -/

lemma airy_I_mul_omega : I * airyOmega = -airyEps := by
  apply Complex.ext
  · simp [airyOmega, airyEps]
  · simp [airyOmega, airyEps]; ring

lemma airy_I_mul_omega_sq : I * airyOmega ^ 2 = (starRingEnd ℂ) airyEps := by
  have : airyOmega ^ 2 = (starRingEnd ℂ) airyOmega := conj_airyOmega.symm
  rw [this]
  apply Complex.ext
  · simp [airyOmega, airyEps]
  · simp [airyOmega, airyEps]; ring

/-- `Bi(z) - i Ai(z) = 2 ε̄ Ai(ω² z)` (DLMF 9.2.10). -/
theorem airyBiC_sub_I_mul_airyAiC (z : ℂ) :
    airyBiC z - I * airyAiC z = 2 * (starRingEnd ℂ) airyEps * airyAiC (airyOmega ^ 2 * z) := by
  have h := airyAiC_rotation z
  have hA : airyAiC z = -(airyOmega * airyAiC (airyOmega * z)) - airyOmega ^ 2 * airyAiC (airyOmega ^ 2 * z) := by
    linear_combination h
  unfold airyBiC
  rw [hA]
  have h1 := airy_I_mul_omega
  have h2 := airy_I_mul_omega_sq
  linear_combination (airyAiC (airyOmega * z)) * h1 + (airyAiC (airyOmega ^ 2 * z)) * h2

/-- `Bi(z) + i Ai(z) = 2 ε Ai(ω z)` (DLMF 9.2.10). -/
theorem airyBiC_add_I_mul_airyAiC (z : ℂ) :
    airyBiC z + I * airyAiC z = 2 * airyEps * airyAiC (airyOmega * z) := by
  have h := airyAiC_rotation z
  have hA : airyAiC z = -(airyOmega * airyAiC (airyOmega * z)) - airyOmega ^ 2 * airyAiC (airyOmega ^ 2 * z) := by
    linear_combination h
  unfold airyBiC
  rw [hA]
  have h1 := airy_I_mul_omega
  have h2 := airy_I_mul_omega_sq
  linear_combination (-airyAiC (airyOmega * z)) * h1 + (-airyAiC (airyOmega ^ 2 * z)) * h2

/-! ### `(ω² u)^{3/2} = -u^{3/2}` in the closed upper half plane -/

lemma airyIm_cpow_half_nonneg {u : ℂ} (h : 0 ≤ u.im) : 0 ≤ (u ^ (1 / 2 : ℂ)).im := by
  rcases eq_or_ne u 0 with rfl | hu
  · simp
  rw [Complex.cpow_def_of_ne_zero hu, Complex.exp_im]
  apply mul_nonneg (Real.exp_pos _).le
  have harg : (Complex.log u * (1 / 2 : ℂ)).im = u.arg / 2 := by
    simp [Complex.log_im]; ring
  rw [harg]
  apply Real.sin_nonneg_of_nonneg_of_le_pi
  · have := Complex.arg_nonneg_iff.mpr h; linarith
  · have := Complex.arg_le_pi u; linarith [Real.pi_pos]

lemma airyOmega_sq_eq_neg_eps_sq : airyOmega ^ 2 = -(airyEps ^ 2) := by
  rw [airyEps_sq]; ring

lemma neg_I_mul_eps_cube : (-(I * airyEps)) ^ 3 = -1 := by
  have h3 := airyEps_cube
  have e : (-(I * airyEps)) ^ 3 = -(I ^ 3 * airyEps ^ 3) := by ring
  rw [e, h3]
  have : I ^ 3 * I = 1 := by rw [← pow_succ]; norm_num [pow_succ, Complex.I_sq]
  linear_combination -this

lemma neg_I_mul_eps_sq : (-(I * airyEps)) ^ 2 = airyOmega ^ 2 := by
  rw [airyOmega_sq_eq_neg_eps_sq]
  have : (-(I * airyEps)) ^ 2 = I ^ 2 * airyEps ^ 2 := by ring
  rw [this, Complex.I_sq]; ring

lemma re_neg_I_eps_mul {w : ℂ} (ha : 0 ≤ w.re) (hb : 0 ≤ w.im) (hw : w ≠ 0) :
    0 < (-(I * airyEps) * w).re := by
  have : (-(I * airyEps) * w).re = 1 / 2 * w.re + √3 / 2 * w.im := by
    simp [airyEps, Complex.mul_re]; ring
  rw [this]
  by_contra hcon
  have h1 : w.re = 0 := by nlinarith [Real.sqrt_nonneg 3]
  have h2 : w.im = 0 := by
    have : 0 < √3 := Real.sqrt_pos.mpr (by norm_num)
    nlinarith
  exact hw (Complex.ext (by simpa using h1) (by simpa using h2))

/-- For `Im u ≥ 0`: `Re (ω² u)^{3/2} = - Re u^{3/2}`. -/
theorem re_cpow_three_halves_omega_sq {u : ℂ} (h : 0 ≤ u.im) :
    ((airyOmega ^ 2 * u) ^ (3 / 2 : ℂ)).re = -(u ^ (3 / 2 : ℂ)).re := by
  rcases eq_or_ne u 0 with rfl | hu
  · simp
  set w := u ^ (1 / 2 : ℂ) with hw
  have hw0 : w ≠ 0 := by
    intro h0
    have := cpow_half_sq u
    rw [← hw, h0] at this
    exact hu (by simpa using this.symm)
  have hre : 0 ≤ w.re := cpow_half_re_nonneg u
  have him : 0 ≤ w.im := airyIm_cpow_half_nonneg h
  have hv := re_neg_I_eps_mul hre him hw0
  set p := (airyOmega ^ 2 * u) ^ (1 / 2 : ℂ) with hp
  have hp2 : p ^ 2 = (-(I * airyEps) * w) ^ 2 := by
    rw [hp, cpow_half_sq, mul_pow, neg_I_mul_eps_sq]
    congr 1
    exact (cpow_half_sq u).symm
  have hpre : 0 ≤ p.re := cpow_half_re_nonneg _
  have hpv : p = -(I * airyEps) * w := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hp2 with h1 | h1
    · exact h1
    · exfalso
      rw [h1] at hpre
      simp only [Complex.neg_re] at hpre
      linarith
  rw [← cpow_half_cube, ← hp, hpv, mul_pow, neg_I_mul_eps_cube, cpow_half_cube]
  simp

/-! ### The ratio bounds -/

lemma airySqrtRe_conj (z : ℂ) : airySqrtRe ((starRingEnd ℂ) z) = airySqrtRe z := by
  have e1 := airySqrtRe_sq_sub z
  have e2 := airySqrtRe_sq_add z
  have f1 := airySqrtRe_sq_sub ((starRingEnd ℂ) z)
  have f2 := airySqrtRe_sq_add ((starRingEnd ℂ) z)
  rw [Complex.norm_conj] at f2
  have h0 := airySqrtRe_nonneg z
  have h0' := airySqrtRe_nonneg ((starRingEnd ℂ) z)
  have : airySqrtRe ((starRingEnd ℂ) z) ^ 2 = airySqrtRe z ^ 2 := by
    simp only [Complex.conj_re] at f1
    nlinarith
  exact (sq_eq_sq₀ h0' h0).mp this

lemma airyEnv_conj (z : ℂ) : airyEnv ((starRingEnd ℂ) z) = airyEnv z := by
  unfold airyEnv
  rw [re_cpow_three_halves_eq, re_cpow_three_halves_eq, airySqrtRe_conj, Complex.conj_re]

theorem airyEnv_omega_sq {u : ℂ} (h : 0 ≤ u.im) : airyEnv (airyOmega ^ 2 * u) = (airyEnv u)⁻¹ := by
  unfold airyEnv
  rw [re_cpow_three_halves_omega_sq h, ← Real.exp_neg]
  congr 1; ring

/-- `‖Bi(u) - i Ai(u)‖² ≤ 36 (1+‖u‖)^{-1/2} / e(u)` for `Im u ≥ 0`. -/
theorem norm_airyBiC_sub_I_mul_sq_le {u : ℂ} (h : 0 ≤ u.im) :
    ‖airyBiC u - I * airyAiC u‖ ^ 2 ≤ 36 * (1 + ‖u‖) ^ (-(1 / 2) : ℝ) / airyEnv u := by
  rw [airyBiC_sub_I_mul_airyAiC, norm_mul, norm_mul, norm_conj_airyEps]
  have := airyAiC_norm_sq_le (airyOmega ^ 2 * u)
  rw [airyEnv_omega_sq h, norm_mul, norm_airyOmega_sq, one_mul] at this
  have e : ‖(2 : ℂ)‖ * 1 * ‖airyAiC (airyOmega ^ 2 * u)‖ = 2 * ‖airyAiC (airyOmega ^ 2 * u)‖ := by
    simp
  rw [e, mul_pow]
  calc (2 : ℝ) ^ 2 * ‖airyAiC (airyOmega ^ 2 * u)‖ ^ 2
      ≤ 2 ^ 2 * (9 * (1 + ‖u‖) ^ (-(1 / 2) : ℝ) * (airyEnv u)⁻¹) := by gcongr
    _ = _ := by field_simp; ring

/-- `R_+ = (Bi - iAi)/Ai` is `O(1/e)` wherever the good-circle bound holds, in the closed upper half plane:
`‖(Bi(u) - i Ai(u))/Ai(u)‖ · e(u) ≤ 30 √π`. -/
theorem airy_Rplus_bound {u : ℂ} (hu : 0 ≤ u.im)
    (hg : 1 / (25 * π) * (1 + ‖u‖) ^ (-(1 / 2) : ℝ) * airyEnv u ≤ ‖airyAiC u‖ ^ 2) :
    ‖(airyBiC u - I * airyAiC u) / airyAiC u‖ * airyEnv u ≤ 30 * √π := by
  set p := (1 + ‖u‖) ^ (-(1 / 2) : ℝ) with hp
  have hp0 : 0 < p := Real.rpow_pos_of_pos (by positivity) _
  have he := airyEnv_pos u
  have hpi := Real.pi_pos
  have hD : 0 < ‖airyAiC u‖ ^ 2 := lt_of_lt_of_le (by positivity) hg
  have hD' : 0 < ‖airyAiC u‖ := by
    rcases (norm_nonneg (airyAiC u)).lt_or_eq with h | h
    · exact h
    · rw [← h] at hD; simp at hD
  have hN := norm_airyBiC_sub_I_mul_sq_le hu
  rw [norm_div]
  rw [← hp] at hN
  have hsq : (‖airyBiC u - I * airyAiC u‖ / ‖airyAiC u‖ * airyEnv u) ^ 2 ≤ (30 * √π) ^ 2 := by
    rw [mul_pow, div_pow, mul_pow, Real.sq_sqrt hpi.le]
    rw [div_mul_eq_mul_div, div_le_iff₀ hD]
    have h1 : ‖airyBiC u - I * airyAiC u‖ ^ 2 * airyEnv u ^ 2 ≤ 36 * p * airyEnv u := by
      calc ‖airyBiC u - I * airyAiC u‖ ^ 2 * airyEnv u ^ 2 ≤ 36 * p / airyEnv u * airyEnv u ^ 2 := by
            gcongr
        _ = 36 * p * airyEnv u := by field_simp
    have h2 : 36 * p * airyEnv u ≤ 30 ^ 2 * π * ‖airyAiC u‖ ^ 2 := by
      have : 36 * p * airyEnv u = 900 * π * (1 / (25 * π) * p * airyEnv u) := by field_simp; ring
      rw [this]
      nlinarith [mul_le_mul_of_nonneg_left hg (by positivity : (0 : ℝ) ≤ 900 * π)]
    linarith
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp hsq

/-- `R_- = (Bi + iAi)/Ai`, lower half plane (conjugation). -/
theorem airy_Rminus_bound {u : ℂ} (hu : u.im ≤ 0)
    (hg : 1 / (25 * π) * (1 + ‖u‖) ^ (-(1 / 2) : ℝ) * airyEnv u ≤ ‖airyAiC u‖ ^ 2) :
    ‖(airyBiC u + I * airyAiC u) / airyAiC u‖ * airyEnv u ≤ 30 * √π := by
  have hc : 0 ≤ ((starRingEnd ℂ) u).im := by simpa using hu
  have hg' : 1 / (25 * π) * (1 + ‖(starRingEnd ℂ) u‖) ^ (-(1 / 2) : ℝ) * airyEnv ((starRingEnd ℂ) u) ≤
      ‖airyAiC ((starRingEnd ℂ) u)‖ ^ 2 := by
    rw [Complex.norm_conj, airyEnv_conj, ← conj_airyAiC, Complex.norm_conj]; exact hg
  have := airy_Rplus_bound hc hg'
  have e : (airyBiC u + I * airyAiC u) / airyAiC u =
      (starRingEnd ℂ) ((airyBiC ((starRingEnd ℂ) u) - I * airyAiC ((starRingEnd ℂ) u)) /
        airyAiC ((starRingEnd ℂ) u)) := by
    rw [map_div₀, map_sub, map_mul, conj_airyBiC, conj_airyAiC, Complex.conj_I, Complex.conj_conj]
    ring
  rw [e, Complex.norm_conj, ← airyEnv_conj u]
  exact this

/-- **Good circles with the Hermite-Biehler ratio bounds** (inputs to the residue/defect formula,
`AIRY_POISSON.md` Theorem D): for every `k ≥ 10` there is `r ∈ [k, k+1]` such that on `|u| = r`,
`Ai(u) ≠ 0`, `(1/(25π))(1+r)^{-1/2} e(u) ≤ ‖Ai(u)‖²`, `‖(Bi - iAi)/Ai‖ e ≤ 30√π` (`Im u ≥ 0`) and
`‖(Bi + iAi)/Ai‖ e ≤ 30√π` (`Im u ≤ 0`). -/
theorem good_circle_ratio_bounds (k : ℕ) (hk : 10 ≤ k) :
    ∃ r : ℝ, (k : ℝ) ≤ r ∧ r ≤ k + 1 ∧ ∀ u : ℂ, ‖u‖ = r →
      1 / (25 * π) * (1 + r) ^ (-(1 / 2) : ℝ) * airyEnv u ≤ ‖airyAiC u‖ ^ 2 ∧
      (0 ≤ u.im → ‖(airyBiC u - I * airyAiC u) / airyAiC u‖ * airyEnv u ≤ 30 * √π) ∧
      (u.im ≤ 0 → ‖(airyBiC u + I * airyAiC u) / airyAiC u‖ * airyEnv u ≤ 30 * √π) := by
  obtain ⟨r, h1, h2, h⟩ := good_circle_exists k hk
  refine ⟨r, h1, h2, fun u hu => ⟨h u hu, fun hi => ?_, fun hi => ?_⟩⟩
  · exact airy_Rplus_bound hi (hu ▸ h u hu)
  · exact airy_Rminus_bound hi (hu ▸ h u hu)

/-- info: 'FormalResearch.Special.airyBiC_sub_I_mul_airyAiC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyBiC_sub_I_mul_airyAiC

/-- info: 'FormalResearch.Special.re_cpow_three_halves_omega_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.re_cpow_three_halves_omega_sq

/-- info: 'FormalResearch.Special.good_circle_ratio_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.good_circle_ratio_bounds

end FormalResearch.Special
