module

public import FormalResearch.Special.AiryAsymSaddle
public import FormalResearch.Special.AiryEnvCalculus

/-!
# Sector asymptotics of `Ai` and `Ai'` with explicit relative remainder

The second-order saddle-point estimate of `AiryAsymSaddle` holds for every `w` with `Re w > 0`.  On the
sector `Re w ≥ s ‖w‖` (`0 < s ≤ 1`; for `z = w²` this is `|arg z| ≤ π - 2 arccos s`, equivalently
`Re z ≥ (2s² - 1)‖z‖`) one has `ρ = Re w ≥ s ‖w‖`, and the absolute remainder
`(5/(96√π)) ‖e^{-(2/3)w³}‖ ρ^{-7/2}` becomes a *relative* remainder `O(‖w‖^{-3}) = O(|z|^{-3/2})`.

Write `L(w) = (1/(2π)) e^{-(2/3)w³} (π/w)^{1/2}` (so `L = e^{-ζ}/(2√π w^{1/2})`, `ζ = (2/3) z^{3/2}`),
`L'(w) = -(w) L(w)`.  Proved here (DLMF 9.7.5/9.7.6 with explicit constants, no Olver theory):

* `norm_airyAiC_sq_sub_lead_le` : `‖Ai(w²) - L(w)‖ ≤ η(s,‖w‖) ‖L(w)‖`, `η = (5/48)/(s³ √s ‖w‖³)`;
* `norm_deriv_airyAiC_sq_add_lead_le` : `‖Ai'(w²) + w L(w)‖ ≤ (17/48)/(s³√s‖w‖³) ‖w L(w)‖`;
* z-form (`z = w²`, `w = z^{1/2}` principal): `airyAiC_sector_asymptotic`
  `‖Ai(z) - Λ(z)‖ ≤ (5/48)/(s³√s ‖z‖^{3/2}) ‖Λ(z)‖`, with `‖Λ(z)‖² = e(z)/(4π √‖z‖)`
  (`norm_airyAiLead_sq`), `Λ = airyAiLead`;
* lower bound `airyAiC_sq_ge_sector`: if `(5/48)/(s³√s ‖z‖^{3/2}) ≤ 1/2` then
  `‖Ai(z)‖² ≥ e(z) / (16 π √‖z‖)`.

Numerical check (mpmath, 30 digits; `s ∈ {1/2, 0.2588, 0.8}`, `‖w‖ ∈ {0.5,…,20}`, 41 angles each across
the whole sector): the ratio (actual relative error)/(stated bound) is at most `0.47` for `Ai` and `0.22` for
`Ai'` (bound in the sharper form `(5/48)‖w‖^{1/2}ρ^{-7/2} + (1/4)‖w‖^{-1/2}ρ^{-5/2}`).
The constant `5/48` is not slack: at `s = 1` (real `w`) the ratio tends to `1` as `‖w‖ → ∞`, since the true relative error
is `5/(72ζ)`; the ratios `0.47`, `0.22` hold for the listed `s` only.

Not formalised: higher terms of the expansion; the sector `|arg z| > π - 2 arccos s` (see
`AiryAsymNegComplex`); the value of the optimal constants.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.Special

/-- The leading term `L(w) = (1/(2π)) e^{-(2/3) w³} (π/w)^{1/2}` of `Ai(w²)`. -/
noncomputable def airyLead (w : ℂ) : ℂ :=
  (1 / (2 * (π : ℂ))) * cexp (-(2 / 3) * w ^ 3) * (π / w) ^ (1 / 2 : ℂ)

lemma norm_airyLead {w : ℂ} :
    ‖airyLead w‖ = 1 / (2 * π) * ‖cexp (-(2 / 3) * w ^ 3)‖ * √(π / ‖w‖) := by
  unfold airyLead
  have h1 : ‖(1 / (2 * (π : ℂ)))‖ = 1 / (2 * π) := by
    rw [norm_div, norm_one, norm_mul]; simp [abs_of_pos Real.pi_pos]
  have h2 : ‖(π : ℂ) / w‖ = π / ‖w‖ := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [norm_mul, norm_mul, norm_cpow_half, h1, h2]

lemma airySector_rem_aux {s R ρ : ℝ} (hs : 0 < s) (hR : 0 < R) (hρ : s * R ≤ ρ) (k : ℕ) :
    √(π / ρ) / ρ ^ k ≤ √(π / R) / (s ^ k * √s * R ^ k) := by
  have hρ0 : 0 < ρ := lt_of_lt_of_le (by positivity) hρ
  rw [Real.sqrt_div Real.pi_pos.le, Real.sqrt_div Real.pi_pos.le, div_div, div_div]
  apply div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (by positivity)
  have h1 : √s * √R ≤ √ρ := by
    rw [← Real.sqrt_mul hs.le]; exact Real.sqrt_le_sqrt hρ
  have h2 : (s * R) ^ k ≤ ρ ^ k := pow_le_pow_left₀ (by positivity) hρ k
  calc √R * (s ^ k * √s * R ^ k) = (√s * √R) * (s * R) ^ k := by ring
    _ ≤ √ρ * ρ ^ k := by gcongr

/-- **Sector asymptotics for `Ai(w²)` with explicit relative remainder.** For `0 < s` and `s‖w‖ ≤ Re w`,
`‖Ai(w²) - L(w)‖ ≤ (5/48)/(s³ √s ‖w‖³) · ‖L(w)‖`. -/
theorem norm_airyAiC_sq_sub_lead_le {w : ℂ} {s : ℝ} (hs : 0 < s) (hw : s * ‖w‖ ≤ w.re)
    (hw0 : 0 < w.re) :
    ‖airyAiC (w ^ 2) - airyLead w‖ ≤ 5 / 48 / (s ^ 3 * √s * ‖w‖ ^ 3) * ‖airyLead w‖ := by
  have hR : 0 < ‖w‖ := norm_pos_iff.mpr (fun h => by simp [h] at hw0)
  have h := norm_airyAiC_sq_sub_le hw0
  have h2 := airySector_rem_aux hs hR hw 3
  refine h.trans ?_
  rw [norm_airyLead]
  have e : 5 / 48 / (s ^ 3 * √s * ‖w‖ ^ 3) * (1 / (2 * π) * ‖cexp (-(2 / 3) * w ^ 3)‖ * √(π / ‖w‖)) =
      1 / (2 * π) * ‖cexp (-(2 / 3) * w ^ 3)‖ * (5 / 48 * (√(π / ‖w‖) / (s ^ 3 * √s * ‖w‖ ^ 3))) := by
    ring
  rw [e]
  gcongr

/-- `-w L(w)` is the leading term of `Ai'(w²)`; for `0 < s ≤ 1`, `s‖w‖ ≤ Re w`:
`‖Ai'(w²) + w L(w)‖ ≤ (17/48)/(s³ √s ‖w‖³) ‖w L(w)‖`. -/
theorem norm_deriv_airyAiC_sq_add_lead_le {w : ℂ} {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (hw : s * ‖w‖ ≤ w.re) (hw0 : 0 < w.re) :
    ‖deriv airyAiC (w ^ 2) + w * airyLead w‖ ≤
      17 / 48 / (s ^ 3 * √s * ‖w‖ ^ 3) * ‖w * airyLead w‖ := by
  have hR : 0 < ‖w‖ := norm_pos_iff.mpr (fun h => by simp [h] at hw0)
  have h := norm_deriv_airyAiC_sq_add_le hw0
  have h3 := airySector_rem_aux hs hR hw 3
  have h2 := airySector_rem_aux hs hR hw 2
  have e0 : deriv airyAiC (w ^ 2) + w * airyLead w =
      deriv airyAiC (w ^ 2) +
        (1 / (2 * (π : ℂ))) * cexp (-(2 / 3) * w ^ 3) * (w * (π / w) ^ (1 / 2 : ℂ)) := by
    unfold airyLead; ring
  rw [e0]
  refine h.trans ?_
  rw [norm_mul, norm_airyLead]
  set E := ‖cexp (-(2 / 3) * w ^ 3)‖
  set R := ‖w‖
  have hE : 0 ≤ E := norm_nonneg _
  have hs3 : 0 < s ^ 3 * √s * R ^ 3 := by positivity
  have hs2 : 0 < s ^ 2 * √s * R ^ 2 := by positivity
  have t2 : √(π / R) / (s ^ 2 * √s * R ^ 2) ≤ R * (√(π / R) / (s ^ 3 * √s * R ^ 3)) := by
    have e1 : R * (√(π / R) / (s ^ 3 * √s * R ^ 3)) = √(π / R) / (s ^ 3 * √s * R ^ 2) := by
      field_simp
    rw [e1]
    apply div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (by positivity)
    have : s ^ 3 ≤ s ^ 2 := by nlinarith [sq_nonneg s]
    have h0 := Real.sqrt_nonneg s
    have h1 : 0 ≤ R ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this h0) h1
  have fin : R * (5 / 48 * (√(π / w.re) / w.re ^ 3)) + 1 / 4 * (√(π / w.re) / w.re ^ 2) ≤
      17 / 48 / (s ^ 3 * √s * R ^ 3) * (R * √(π / R)) := by
    have e2 : 17 / 48 / (s ^ 3 * √s * R ^ 3) * (R * √(π / R)) =
        17 / 48 * (R * (√(π / R) / (s ^ 3 * √s * R ^ 3))) := by ring
    rw [e2]
    nlinarith [mul_le_mul_of_nonneg_left h3 hR.le]
  have hc : 0 ≤ 1 / (2 * π) * E := by positivity
  refine (mul_le_mul_of_nonneg_left fin hc).trans (le_of_eq ?_)
  ring

/-! ### The `z`-form -/

/-- The leading term `Λ(z) = e^{-ζ}/(2√π z^{1/4})`, `ζ = (2/3) z^{3/2}`, of `Ai(z)`, written as `L(z^{1/2})`. -/
noncomputable def airyAiLead (z : ℂ) : ℂ := airyLead (z ^ (1 / 2 : ℂ))

/-- The leading term `-z^{1/2} Λ(z)` of `Ai'(z)`. -/
noncomputable def airyAiDerivLead (z : ℂ) : ℂ := -(z ^ (1 / 2 : ℂ) * airyAiLead z)

lemma airyNorm_cpow_half_pow_three (z : ℂ) : ‖z ^ (1 / 2 : ℂ)‖ ^ 3 = ‖z‖ ^ (3 / 2 : ℝ) := by
  rw [norm_cpow_half, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
  norm_num

lemma norm_cexp_airyLead (z : ℂ) :
    ‖cexp (-(2 / 3) * (z ^ (1 / 2 : ℂ)) ^ 3)‖ ^ 2 = airyEnv z := by
  rw [Complex.norm_exp, cpow_half_cube, airyEnv, ← Real.exp_nat_mul]
  congr 1
  simp only [Complex.mul_re, Complex.neg_re, Complex.div_re, Complex.neg_im]
  norm_num
  ring

/-- `‖Λ(z)‖² = e(z) / (4π √‖z‖)`. -/
theorem norm_airyAiLead_sq (z : ℂ) :
    ‖airyAiLead z‖ ^ 2 = airyEnv z / (4 * π * √‖z‖) := by
  unfold airyAiLead
  rw [norm_airyLead, norm_cpow_half]
  by_cases hz : ‖z‖ = 0
  · simp [hz]
  have hpos : 0 < √‖z‖ := Real.sqrt_pos.mpr (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz))
  have h1 : (1 / (2 * π) * ‖cexp (-(2 / 3) * (z ^ (1 / 2 : ℂ)) ^ 3)‖ * √(π / √‖z‖)) ^ 2 =
      (1 / (2 * π)) ^ 2 * ‖cexp (-(2 / 3) * (z ^ (1 / 2 : ℂ)) ^ 3)‖ ^ 2 * (π / √‖z‖) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
  rw [h1, norm_cexp_airyLead]
  field_simp
  ring

/-- **Sector asymptotics, `z`-form.** If `0 < s ≤ 1`, `z ≠ 0`, `Re z ≥ (2s²-1)‖z‖`, then
`‖Ai(z) - Λ(z)‖ ≤ (5/48)/(s³ √s ‖z‖^{3/2}) ‖Λ(z)‖`.  (`|arg z| ≤ π - 2 arccos s`.) -/
theorem airyAiC_sector_asymptotic {z : ℂ} {s : ℝ} (hs : 0 < s) (hz : 0 < ‖z‖)
    (hre : (2 * s ^ 2 - 1) * ‖z‖ ≤ z.re) :
    ‖airyAiC z - airyAiLead z‖ ≤ 5 / 48 / (s ^ 3 * √s * ‖z‖ ^ (3 / 2 : ℝ)) * ‖airyAiLead z‖ := by
  have e1 := airySqrtRe_sq_sub z
  have e2 := airySqrtRe_sq_add z
  have hw : s * ‖z ^ (1 / 2 : ℂ)‖ ≤ (z ^ (1 / 2 : ℂ)).re := by
    have hn : ‖z ^ (1 / 2 : ℂ)‖ ^ 2 = ‖z‖ := norm_cpow_half_sq z
    have h0 := airySqrtRe_nonneg z
    have : (s * ‖z ^ (1 / 2 : ℂ)‖) ^ 2 ≤ (z ^ (1 / 2 : ℂ)).re ^ 2 := by
      have : (z ^ (1 / 2 : ℂ)).re = airySqrtRe z := rfl
      rw [this, mul_pow, hn]
      nlinarith
    exact (pow_le_pow_iff_left₀ (by positivity) h0 two_ne_zero).mp this
  have hw0 : 0 < (z ^ (1 / 2 : ℂ)).re := by
    have : 0 < ‖z ^ (1 / 2 : ℂ)‖ := by rw [norm_cpow_half]; exact Real.sqrt_pos.mpr hz
    nlinarith
  have := norm_airyAiC_sq_sub_lead_le hs hw hw0
  rw [cpow_half_sq, airyNorm_cpow_half_pow_three] at this
  exact this

/-- The shared sector hypotheses give `s‖w‖ ≤ Re w` and `0 < Re w` for `w = z^{1/2}`. -/
lemma sector_root_facts {z : ℂ} {s : ℝ} (hs : 0 < s) (hz : 0 < ‖z‖)
    (hre : (2 * s ^ 2 - 1) * ‖z‖ ≤ z.re) :
    s * ‖z ^ (1 / 2 : ℂ)‖ ≤ (z ^ (1 / 2 : ℂ)).re ∧ 0 < (z ^ (1 / 2 : ℂ)).re := by
  have e1 := airySqrtRe_sq_sub z
  have e2 := airySqrtRe_sq_add z
  have hn : ‖z ^ (1 / 2 : ℂ)‖ ^ 2 = ‖z‖ := norm_cpow_half_sq z
  have h0 := airySqrtRe_nonneg z
  have hw : s * ‖z ^ (1 / 2 : ℂ)‖ ≤ (z ^ (1 / 2 : ℂ)).re := by
    have : (s * ‖z ^ (1 / 2 : ℂ)‖) ^ 2 ≤ (z ^ (1 / 2 : ℂ)).re ^ 2 := by
      have : (z ^ (1 / 2 : ℂ)).re = airySqrtRe z := rfl
      rw [this, mul_pow, hn]
      nlinarith
    exact (pow_le_pow_iff_left₀ (by positivity) h0 two_ne_zero).mp this
  refine ⟨hw, ?_⟩
  have : 0 < ‖z ^ (1 / 2 : ℂ)‖ := by rw [norm_cpow_half]; exact Real.sqrt_pos.mpr hz
  nlinarith

/-- **Sector asymptotics for `Ai'`, `z`-form** (`0 < s ≤ 1`, `Re z ≥ (2s²-1)‖z‖`):
`‖Ai'(z) - Λ'(z)‖ ≤ (17/48)/(s³ √s ‖z‖^{3/2}) ‖Λ'(z)‖`, `Λ' = -z^{1/2} Λ`. -/
theorem deriv_airyAiC_sector_asymptotic {z : ℂ} {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (hz : 0 < ‖z‖)
    (hre : (2 * s ^ 2 - 1) * ‖z‖ ≤ z.re) :
    ‖deriv airyAiC z - airyAiDerivLead z‖ ≤
      17 / 48 / (s ^ 3 * √s * ‖z‖ ^ (3 / 2 : ℝ)) * ‖airyAiDerivLead z‖ := by
  obtain ⟨hw, hw0⟩ := sector_root_facts hs hz hre
  have := norm_deriv_airyAiC_sq_add_lead_le hs hs1 hw hw0
  rw [cpow_half_sq, airyNorm_cpow_half_pow_three] at this
  unfold airyAiDerivLead airyAiLead
  rw [norm_neg, sub_neg_eq_add]
  exact this

/-- `‖Λ'(z)‖² = √‖z‖ e(z)/(4π)`. -/
theorem norm_airyAiDerivLead_sq (z : ℂ) :
    ‖airyAiDerivLead z‖ ^ 2 = √‖z‖ * airyEnv z / (4 * π) := by
  unfold airyAiDerivLead
  rw [norm_neg, norm_mul, mul_pow, norm_cpow_half, norm_airyAiLead_sq, Real.sq_sqrt (norm_nonneg _)]
  by_cases hz : ‖z‖ = 0
  · simp [hz]
  have hpos : 0 < √‖z‖ := Real.sqrt_pos.mpr (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz))
  field_simp
  rw [Real.sq_sqrt (norm_nonneg _)]
  ring

/-- **Lower bound for `Ai` in a sector.** If `η := (5/48)/(s³ √s ‖z‖^{3/2}) ≤ 1/2`, then
`‖Ai(z)‖² ≥ e(z)/(16 π √‖z‖)`. -/
theorem airyAiC_sq_ge_sector {z : ℂ} {s : ℝ} (hs : 0 < s) (hz : 0 < ‖z‖)
    (hre : (2 * s ^ 2 - 1) * ‖z‖ ≤ z.re)
    (hη : 5 / 48 / (s ^ 3 * √s * ‖z‖ ^ (3 / 2 : ℝ)) ≤ 1 / 2) :
    airyEnv z / (16 * π * √‖z‖) ≤ ‖airyAiC z‖ ^ 2 := by
  have h := airyAiC_sector_asymptotic hs hz hre
  set Λ := airyAiLead z
  have hL := norm_nonneg Λ
  have h1 : ‖Λ‖ / 2 ≤ ‖airyAiC z‖ := by
    have := norm_sub_norm_le Λ (Λ - airyAiC z)
    have h2 : ‖airyAiC z - Λ‖ ≤ ‖Λ‖ / 2 := by
      refine h.trans ?_
      nlinarith
    have h3 : ‖Λ - airyAiC z‖ = ‖airyAiC z - Λ‖ := norm_sub_rev _ _
    simp only [sub_sub_cancel] at this
    linarith
  have h2 := norm_airyAiLead_sq z
  have : (‖Λ‖ / 2) ^ 2 ≤ ‖airyAiC z‖ ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
  calc airyEnv z / (16 * π * √‖z‖) = (‖Λ‖ / 2) ^ 2 := by
        rw [div_pow, h2]
        have : 0 < √‖z‖ := Real.sqrt_pos.mpr hz
        field_simp; ring
    _ ≤ _ := this

/-- info: 'FormalResearch.Special.norm_airyAiC_sq_sub_lead_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.norm_airyAiC_sq_sub_lead_le

/-- info: 'FormalResearch.Special.norm_deriv_airyAiC_sq_add_lead_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.norm_deriv_airyAiC_sq_add_lead_le

/-- info: 'FormalResearch.Special.airyAiC_sector_asymptotic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyAiC_sector_asymptotic

/-- info: 'FormalResearch.Special.deriv_airyAiC_sector_asymptotic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.deriv_airyAiC_sector_asymptotic

/-- info: 'FormalResearch.Special.norm_airyAiLead_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.norm_airyAiLead_sq

/-- info: 'FormalResearch.Special.airyAiC_sq_ge_sector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyAiC_sq_ge_sector

end FormalResearch.Special
