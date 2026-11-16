module

public import FormalResearch.Complex.HadamardAiry
public import FormalResearch.Special.AiryCft2ComboZeros

/-!
# The Hadamard product of `Ai'`

Companion of `Hadamard.airyAiC_hadamard` (the product of `Ai`): `Ai'` is entire of order `3/2` (`airyAiC_deriv_norm_le_exp_rpow`), its zeros
are real, negative and simple (the zeros `a'_n` of `Ai'`: `airyNC_zero_im` for `P = 0`, `Q = 1`, `airyAi'_neg`, `Ai'' = z Ai` with
`Ai(a'_n) ≠ 0`), and `Ai''(0) = 0`, so the exponential factor of the genus-one product is trivial:

`Ai'(z) = Ai'(0) ∏_i (1 - z/b_i) exp (z/b_i)`, `Σ_i |b_i|^{-2} < ∞`   (`airyDeriv_hadamard`),

where `b` is the canonical listing of the zeros of `Ai'` (`Hadamard.ZeroIdx`, `Listing`; every `b_i` is real and negative
and a simple zero, part of the statement of `airyDeriv_hadamard`).  The identification of the listing with the ordered zeros `a'_1 > a'_2 > …`
(`a'_1 ∈ (a_1, 0)`: `airyDeriv_largest_zero`, `a'_{n+1} ∈ (a_{n+1}, a_n)`: `airyAi'_existsUnique_zero_gap`) is not
recorded here.

Proved (axiom-checked); input: `Hadamard.hadamard_exists` (`p = 1`).  The CFT notes use only the Hadamard product of `Ai`
(Lemma ID, `FOLD_TIP_THEOREM.md` seed lemma, via `airyAiC_hadamard` and the Mittag-Leffler expansion `airyAiC_logDeriv_mittagLeffler`); this
file is not needed by them (a closing-the-loop statement).  Not formalised: the product for `Bi` (its zeros are not all real).
-/

@[expose] public section

open Complex Filter Topology Finset Metric Set FormalResearch.Special
open scoped BigOperators Classical

namespace FormalResearch.Special

open FormalResearch.Hadamard

lemma airyC2_rpow_quarter_le (r : ℝ) (hr : 0 ≤ r) : (1 + r) ^ (1 / 4 : ℝ) ≤ 2 * (1 + r ^ (3 / 2 : ℝ)) := by
  by_cases h1 : r ≤ 1
  · have : (1 + r) ^ (1 / 4 : ℝ) ≤ (2 : ℝ) ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
    have h2 : (2 : ℝ) ^ (1 / 4 : ℝ) ≤ 2 := by
      calc (2 : ℝ) ^ (1 / 4 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := Real.rpow_one 2
    have : 0 ≤ r ^ (3 / 2 : ℝ) := Real.rpow_nonneg hr _
    linarith
  · push Not at h1
    have h2 : (1 + r) ^ (1 / 4 : ℝ) ≤ 1 + r := by
      calc (1 + r) ^ (1 / 4 : ℝ) ≤ (1 + r) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
        _ = 1 + r := Real.rpow_one _
    have h3 : r ≤ r ^ (3 / 2 : ℝ) := by
      calc r = r ^ (1 : ℝ) := (Real.rpow_one r).symm
        _ ≤ r ^ (3 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1.le (by norm_num)
    linarith

lemma airyDeriv_growth : GrowthBound (deriv airyAiC) (3 / 2) := by
  refine ⟨10, fun z => ?_⟩
  refine (airyAiC_deriv_norm_le_exp_rpow z).trans ?_
  have hx : 0 ≤ ‖z‖ ^ (3 / 2 : ℝ) := Real.rpow_nonneg (norm_nonneg _) _
  have h1 := airyC2_rpow_quarter_le ‖z‖ (norm_nonneg _)
  have h2 : 1 + ‖z‖ ^ (3 / 2 : ℝ) ≤ Real.exp (‖z‖ ^ (3 / 2 : ℝ)) := by
    have := Real.add_one_le_exp (‖z‖ ^ (3 / 2 : ℝ)); linarith
  have h3 : Real.exp ((2 / 3) * ‖z‖ ^ (3 / 2 : ℝ)) * Real.exp (‖z‖ ^ (3 / 2 : ℝ)) ≤
      Real.exp (10 * ‖z‖ ^ (3 / 2 : ℝ)) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by nlinarith)
  have h4 : 0 < Real.exp ((2 / 3) * ‖z‖ ^ (3 / 2 : ℝ)) := Real.exp_pos _
  calc 5 * (1 + ‖z‖) ^ (1 / 4 : ℝ) * Real.exp (2 / 3 * ‖z‖ ^ (3 / 2 : ℝ))
      ≤ 5 * (2 * Real.exp (‖z‖ ^ (3 / 2 : ℝ))) * Real.exp (2 / 3 * ‖z‖ ^ (3 / 2 : ℝ)) := by
        gcongr; linarith
    _ = 10 * (Real.exp ((2 / 3) * ‖z‖ ^ (3 / 2 : ℝ)) * Real.exp (‖z‖ ^ (3 / 2 : ℝ))) := by ring
    _ ≤ 10 * Real.exp (10 * ‖z‖ ^ (3 / 2 : ℝ)) := by gcongr

lemma differentiable_deriv_airyAiC : Differentiable ℂ (deriv airyAiC) :=
  fun z => (hasDerivAt_deriv_airyAiC z).differentiableAt

lemma airyC2_deriv_zero_ne : deriv airyAiC 0 ≠ 0 := by
  have h := deriv_airyAiC_ofReal 0
  simp only [Complex.ofReal_zero] at h
  rw [h]
  exact_mod_cast (airyAi'_neg (le_refl (0 : ℝ))).ne

/-- Zeros of `Ai'` in `ℂ` are real, negative, and simple. -/
theorem airyDeriv_zero_real_neg {w : ℂ} (hw : deriv airyAiC w = 0) :
    w.im = 0 ∧ w.re < 0 ∧ deriv (deriv airyAiC) w ≠ 0 := by
  have h0 : airyNC 0 1 w = 0 := by simp [airyNC, hw]
  have him := airyNC_zero_im 0 1 one_ne_zero h0
  have e : w = (w.re : ℂ) := Complex.ext (by simp) (by simp [him])
  have hx : airyAi' w.re = 0 := by
    have := hw
    rw [e, deriv_airyAiC_ofReal] at this
    exact_mod_cast this
  have hneg : w.re < 0 := by
    by_contra hge
    exact (airyAi'_neg (not_lt.mp hge)).ne hx
  refine ⟨him, hneg, ?_⟩
  have hd : deriv (deriv airyAiC) w = w * airyAiC w := (hasDerivAt_deriv_airyAiC w).deriv
  rw [hd]
  have hA : airyAiC w ≠ 0 := by
    intro h
    have := airyNC_ne_zero_of_airy_zero 0 1 one_ne_zero h
    exact this h0
  have hw0 : w ≠ 0 := by
    intro h; rw [h] at hneg; simp at hneg
  exact mul_ne_zero hw0 hA

/-- **The Hadamard product of `Ai'`.** For the canonical listing `b` of the zeros of `Ai'`:
`Σ |b_i|^{-2} < ∞`, every `b_i` is real, negative and a simple zero of `Ai'`, and
`Ai'(z) = Ai'(0) ∏_i (1 - z/b_i) exp (z/b_i)` for all `z ∈ ℂ`. -/
theorem airyDeriv_hadamard :
    ∃ b : ZeroIdx (deriv airyAiC) → ℂ, Listing (deriv airyAiC) b ∧ Summable (fun i => (‖b i‖ ^ 2)⁻¹) ∧
      (∀ i, deriv airyAiC (b i) = 0 ∧ (b i).im = 0 ∧ (b i).re < 0 ∧ deriv (deriv airyAiC) (b i) ≠ 0) ∧
      ∀ z : ℂ, deriv airyAiC z = deriv airyAiC 0 * ∏' i, (1 - z / b i) * cexp (z / b i) := by
  have hne : ∃ z, deriv airyAiC z ≠ 0 := ⟨0, airyC2_deriv_zero_ne⟩
  obtain ⟨b, L, hs, c, P, hc, hdeg, hP0, hid⟩ := hadamard_exists differentiable_deriv_airyAiC hne
    (σ := 3 / 2) (by norm_num) airyDeriv_growth
  have hfl : ⌊(3 / 2 : ℝ)⌋₊ = 1 := by
    rw [Nat.floor_eq_iff (by norm_num)]; norm_num
  rw [hfl] at hs hdeg hid
  simp only [E_one] at hid
  have hs2 : Summable (fun i => (‖b i‖ ^ 2)⁻¹) := hs
  have hord0 : analyticOrderNatAt (deriv airyAiC) 0 = 0 := by
    have : analyticOrderAt (deriv airyAiC) 0 = 0 := by
      rw [analyticOrderAt_eq_zero]; exact Or.inr airyC2_deriv_zero_ne
    simp [analyticOrderNatAt, this]
  simp only [hord0, pow_zero, mul_one] at hid
  have hCD : CanonData 1 b := ⟨L.ne_zero, by simpa using hs2⟩
  have hPeval : ∀ z, P.eval z = P.coeff 1 * z := by
    intro z
    rw [Polynomial.eval_eq_sum_range' (n := 2) (by omega)]
    have hc0 : P.coeff 0 = 0 := by simpa [Polynomial.coeff_zero_eq_eval_zero] using hP0
    simp [Finset.sum_range_succ, hc0]
  set Φ : ℂ → ℂ := fun z => ∏' i, (1 - z / b i) * cexp (z / b i) with hΦ
  have hΦE : Φ = canonProd 1 b := by
    funext z; simp [hΦ, canonProd, E_one]
  have hΦd : Differentiable ℂ Φ := by rw [hΦE]; exact differentiable_canonProd hCD
  have hΦ0 : Φ 0 = 1 := by simp [hΦ]
  have hΦ'0 : deriv Φ 0 = 0 := by
    have := logDeriv_canonProd hCD (z := 0) (fun i => (L.ne_zero i).symm)
    rw [← hΦE, logDeriv_apply, hΦ0, div_one] at this
    rw [this]; simp
  have hc0 : c = deriv airyAiC 0 := by
    have := hid 0
    simp only [hPeval, mul_zero, Complex.exp_zero, mul_one] at this
    rw [show (∏' i, (1 - (0 : ℂ) / b i) * cexp ((0 : ℂ) / b i)) = 1 from hΦ0, mul_one] at this
    exact this.symm
  have hb1 : P.coeff 1 = 0 := by
    have hfun : deriv airyAiC = fun z => c * cexp (P.coeff 1 * z) * Φ z :=
      funext fun z => by rw [hid z, hPeval]
    have hd : HasDerivAt (fun z : ℂ => c * cexp (P.coeff 1 * z) * Φ z)
        (c * (cexp (P.coeff 1 * 0) * P.coeff 1) * Φ 0 + c * cexp (P.coeff 1 * 0) * deriv Φ 0) 0 := by
      have h1' : HasDerivAt (fun z : ℂ => P.coeff 1 * z) (P.coeff 1) 0 := by
        simpa using (hasDerivAt_id (0 : ℂ)).const_mul (P.coeff 1)
      have h2' := ((h1'.cexp).const_mul c).fun_mul (hΦd 0).hasDerivAt
      simpa using h2'
    have hderiv : deriv (deriv airyAiC) 0 = c * P.coeff 1 := by
      rw [hfun, hd.deriv]
      simp [hΦ0, hΦ'0]
    have hd0 : deriv (deriv airyAiC) 0 = 0 := by
      have := (hasDerivAt_deriv_airyAiC 0).deriv
      rw [this]; simp
    rw [hd0] at hderiv
    rcases mul_eq_zero.mp hderiv.symm with h | h
    · exact absurd h hc
    · exact h
  refine ⟨b, L, hs2, fun i => ?_, fun z => ?_⟩
  · have hzero : deriv airyAiC (b i) = 0 := by
      by_contra hn
      have hord : analyticOrderNatAt (deriv airyAiC) (b i) = 0 := by
        have : analyticOrderAt (deriv airyAiC) (b i) = 0 := by
          rw [analyticOrderAt_eq_zero]; exact Or.inr hn
        simp [analyticOrderNatAt, this]
      have hc0 := L.ncard_fibre (b i) (L.ne_zero i)
      rw [hord, Set.ncard_eq_zero (L.finite_fibre _)] at hc0
      have : i ∈ b ⁻¹' {b i} := rfl
      rw [hc0] at this
      exact this
    obtain ⟨h1, h2, h3⟩ := airyDeriv_zero_real_neg hzero
    exact ⟨hzero, h1, h2, h3⟩
  · rw [hid z, hc0, hPeval, hb1]; simp

/-- info: 'FormalResearch.Special.airyDeriv_hadamard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyDeriv_hadamard

end FormalResearch.Special
