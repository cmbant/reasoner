module

public import FormalResearch.Special.AiryAsymChi

/-!
# The saddle-point integral of `Ai(w²)` to relative order `w^{-9}` (the `u₂` term)

`AiryAsymChi` expands `e^{-is³/3}` to the Taylor order `3` (remainder `s^{12}/1944`), which gives `Ai(w²)` up to a
relative error `O(w^{-6})`.  For the second-order zero asymptotics (DLMF 9.9.18, `AiryZeroSecondOrder`) the *imaginary
part* of the correction at `w³ = i r³` is needed to relative order `r^{-9}`, so here the expansion is pushed two orders
further:

* `airySO_taylor_le`: `‖e^{ix} - Σ_{m<n} (ix)^m/m!‖ ≤ |x|^n/n!` for all `n` and real `x` (general Taylor remainder, by
  induction from the one-step integration lemma `norm_le_of_hasDerivAt_bound`);
* `norm_saddlePhase_sub_poly6_le`: `‖e^{-is³/3} - (1 - i s³/3 - s⁶/18 + i s⁹/162 + s^{12}/1944 - i s^{15}/29160)‖ ≤ s^{18}/524880`;
* `airySO_integral_twelfth_gauss_complex`: `∫ s^{12} e^{-w s²} = (10395/(64 w⁶)) (π/w)^{1/2}` (complex `w`, `Re w > 0`),
  and `airySO_integral_eighteenth_gauss`: `∫ s^{18} e^{-ρ s²} = (34459425/512) √(π/ρ)/ρ⁹` (real `ρ > 0`);
* **`norm_saddleJ0_fourth_le`**: for `Re w = ρ > 0`
  `‖J₀(w) - (π/w)^{1/2} (1 - 5/(48 w³) + 385/(4608 w⁶))‖ ≤ (34459425/268738560) √(π/ρ)/ρ⁹`,
  where `J₀(w) = ∫ exp(-w s² - i s³/3) ds` (`saddleJ0`); and the same for `Ai(w²)`
  (**`norm_airyAiC_sq_fourth_le`**, via `airyAiC_sq_eq`).

Proved here: all of the above (the coefficients `-5/48` and `385/4608` are the `u₁`, `u₂` of DLMF 9.7.2–9.7.3 after
`w³ = (3/2)ξ`-scaling: `385/4608 · (4/9) = 385/10368 = u₂`).  The general-`N` expansion with the `u₃`, `u₄` terms is `AiryZeroThirdSaddle`.  **Not formalised:**
the terms beyond that, and sector-uniform versions.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.Special

/-! ### Taylor remainder of `e^{ix}` to all orders -/

/-- One integration step: if `p' = i q`, `p 0 = 1` and `‖e^{ix} - q x‖ ≤ |x|^n/n!`, then
`‖e^{ix} - p x‖ ≤ |x|^{n+1}/(n+1)!`. -/
lemma airySO_taylor_step (p q : ℝ → ℂ) (hp : ∀ t, HasDerivAt p (I * q t) t) (hp0 : p 0 = 1) (n : ℕ)
    (hq : ∀ x : ℝ, ‖cexp (I * (x : ℂ)) - q x‖ ≤ |x| ^ n / (n.factorial : ℝ)) (x : ℝ) :
    ‖cexp (I * (x : ℂ)) - p x‖ ≤ |x| ^ (n + 1) / ((n + 1).factorial : ℝ) := by
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => cexp (I * (t : ℂ))) (I * cexp (I * (t : ℂ))) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => I * (t : ℂ)) I t := by
      simpa using ((hasDerivAt_id t).ofReal_comp).const_mul I
    simpa [mul_comm] using h1.cexp
  refine norm_le_of_hasDerivAt_bound (fun t => cexp (I * (t : ℂ)) - p t)
    (fun t => I * (cexp (I * (t : ℂ)) - q t)) n (fun t => ?_) (by simp [hp0]) (fun t => ?_) x
  · refine ((hd t).sub (hp t)).congr_deriv ?_
    ring
  · rw [norm_mul, Complex.norm_I, one_mul]
    exact hq t

/-- The Taylor polynomial of `e^{it}` of degree `< n`. -/
noncomputable def airySO_P (n : ℕ) (t : ℝ) : ℂ :=
  ∑ m ∈ Finset.range n, (I * (t : ℂ)) ^ m / (m.factorial : ℂ)

lemma airySO_P_hasDeriv (n : ℕ) (t : ℝ) : HasDerivAt (airySO_P (n + 1)) (I * airySO_P n t) t := by
  induction n with
  | zero =>
    have e : airySO_P (0 + 1) = fun _ => (1 : ℂ) := by funext t; simp [airySO_P]
    have e0 : airySO_P 0 t = 0 := by simp [airySO_P]
    rw [e, e0, mul_zero]
    exact hasDerivAt_const t (1 : ℂ)
  | succ n ih =>
    have h1 : HasDerivAt (fun t : ℝ => I * (t : ℂ)) I t := by
      simpa using ((hasDerivAt_id t).ofReal_comp).const_mul I
    have h2 : HasDerivAt (fun t : ℝ => (I * (t : ℂ)) ^ (n + 1) / ((n + 1).factorial : ℂ))
        (I * ((I * (t : ℂ)) ^ n / (n.factorial : ℂ))) t := by
      have := (h1.pow (n + 1)).div_const (((n + 1).factorial : ℂ))
      refine this.congr_deriv ?_
      have hf : ((n + 1).factorial : ℂ) = (n + 1) * n.factorial := by
        push_cast [Nat.factorial_succ]; ring
      have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
      have hn1 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      rw [hf]
      simp only [Nat.add_sub_cancel]
      push_cast
      field_simp
    have := ih.add h2
    have e : airySO_P (n + 2) = fun t => airySO_P (n + 1) t +
        (I * (t : ℂ)) ^ (n + 1) / ((n + 1).factorial : ℂ) := by
      funext t; simp only [airySO_P]; rw [Finset.sum_range_succ _ (n + 1)]
    rw [e]
    refine this.congr_deriv ?_
    simp only [airySO_P]
    rw [Finset.sum_range_succ _ n]
    ring

lemma airySO_P_zero (n : ℕ) : airySO_P (n + 1) 0 = 1 := by
  simp only [airySO_P, Complex.ofReal_zero, mul_zero]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro m _ hm; simp [zero_pow hm]
  · intro h; exact absurd (Finset.mem_range.2 (by omega)) h

/-- **Taylor remainder of `e^{ix}` to every order**: `‖e^{ix} - Σ_{m<n} (ix)^m/m!‖ ≤ |x|^n/n!`. -/
theorem airySO_taylor_le (n : ℕ) (x : ℝ) :
    ‖cexp (I * (x : ℂ)) - airySO_P n x‖ ≤ |x| ^ n / (n.factorial : ℝ) := by
  induction n generalizing x with
  | zero => simp [airySO_P, Complex.norm_exp_I_mul_ofReal]
  | succ n ih =>
    exact airySO_taylor_step (airySO_P (n + 1)) (airySO_P n) (fun t => airySO_P_hasDeriv n t)
      (airySO_P_zero n) n ih x

lemma airySO_P_six (x : ℝ) : airySO_P 6 x = 1 + I * (x : ℂ) + (I * (x : ℂ)) ^ 2 / 2 + (I * (x : ℂ)) ^ 3 / 6 +
    (I * (x : ℂ)) ^ 4 / 24 + (I * (x : ℂ)) ^ 5 / 120 := by
  simp [airySO_P, Finset.sum_range_succ, Nat.factorial]

/-- The fifth-order Taylor polynomial of the cubic phase and its remainder. -/
lemma norm_saddlePhase_sub_poly6_le (s : ℝ) :
    ‖saddlePhase s - (1 - I * (s : ℂ) ^ 3 / 3 - (s : ℂ) ^ 6 / 18 + I * (s : ℂ) ^ 9 / 162 +
        (s : ℂ) ^ 12 / 1944 - I * (s : ℂ) ^ 15 / 29160)‖ ≤ s ^ 18 / 524880 := by
  have h := airySO_taylor_le 6 (-(s ^ 3 / 3))
  rw [airySO_P_six] at h
  have e : saddlePhase s - (1 - I * (s : ℂ) ^ 3 / 3 - (s : ℂ) ^ 6 / 18 + I * (s : ℂ) ^ 9 / 162 +
        (s : ℂ) ^ 12 / 1944 - I * (s : ℂ) ^ 15 / 29160) =
      cexp (I * ((-(s ^ 3 / 3) : ℝ) : ℂ)) - (1 + I * ((-(s ^ 3 / 3) : ℝ) : ℂ) +
        (I * ((-(s ^ 3 / 3) : ℝ) : ℂ)) ^ 2 / 2 + (I * ((-(s ^ 3 / 3) : ℝ) : ℂ)) ^ 3 / 6 +
        (I * ((-(s ^ 3 / 3) : ℝ) : ℂ)) ^ 4 / 24 + (I * ((-(s ^ 3 / 3) : ℝ) : ℂ)) ^ 5 / 120) := by
    unfold saddlePhase
    push_cast
    have hI2 : I ^ 2 = -1 := Complex.I_sq
    have hI3 : I ^ 3 = -I := by rw [pow_succ, Complex.I_sq]; ring
    have hI4 : I ^ 4 = 1 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Complex.I_sq]; norm_num
    have hI5 : I ^ 5 = I := by rw [pow_succ, hI4]; ring
    linear_combination ((s : ℂ) ^ 6 / 18) * hI2 + (-(s : ℂ) ^ 9 / 162) * hI3 + ((s : ℂ) ^ 12 / 1944) * hI4 +
      (-(s : ℂ) ^ 15 / 29160) * hI5
  rw [e]
  refine h.trans (le_of_eq ?_)
  rw [abs_neg, Even.pow_abs (by decide : Even 6)]
  norm_num [Nat.factorial]
  ring

/-! ### Gaussian moments of order twelve (complex) and eighteen (real) -/

/-- `∫ s^{12} e^{-w s²} = (10395/(64 w⁶)) (π/w)^{1/2}` for `Re w > 0`. -/
lemma airySO_integral_twelfth_gauss_complex {w : ℂ} (hw : 0 < w.re) :
    ∫ s : ℝ, (s : ℂ) ^ 12 * cexp (-w * (s : ℂ) ^ 2) = 10395 / (64 * w ^ 6) * (π / w) ^ (1 / 2 : ℂ) := by
  have hw0 : w ≠ 0 := fun h => by simp [h] at hw
  have e1 : ∫ s : ℝ, (s : ℂ) ^ 12 * cexp (-w * (s : ℂ) ^ 2) =
      (11 / (2 * w)) * ∫ s : ℝ, (s : ℂ) ^ 10 * cexp (-w * (s : ℂ) ^ 2) := by
    have h := integral_pow_gauss_succ hw 10
    norm_num at h ⊢
    exact h
  have e2 : ∫ s : ℝ, (s : ℂ) ^ 10 * cexp (-w * (s : ℂ) ^ 2) =
      (9 / (2 * w)) * ∫ s : ℝ, (s : ℂ) ^ 8 * cexp (-w * (s : ℂ) ^ 2) := by
    have h := integral_pow_gauss_succ hw 8
    norm_num at h ⊢
    exact h
  have e3 : ∫ s : ℝ, (s : ℂ) ^ 8 * cexp (-w * (s : ℂ) ^ 2) =
      (7 / (2 * w)) * ∫ s : ℝ, (s : ℂ) ^ 6 * cexp (-w * (s : ℂ) ^ 2) := by
    have h := integral_pow_gauss_succ hw 6
    norm_num at h ⊢
    exact h
  rw [e1, e2, e3, integral_sixth_gauss_complex hw]
  field_simp
  ring

/-- `∫ s^{18} e^{-ρ s²} = (34459425/512) √(π/ρ)/ρ⁹` for `ρ > 0`. -/
lemma airySO_integral_eighteenth_gauss {c : ℝ} (hc : 0 < c) :
    ∫ s : ℝ, s ^ 18 * Real.exp (-c * s ^ 2) = 34459425 / 512 * √(π / c) / c ^ 9 := by
  have h := integral_comp_abs (f := fun y : ℝ => y ^ 18 * Real.exp (-c * y ^ 2))
  simp only [sq_abs] at h
  have h18 : ∀ s : ℝ, |s| ^ 18 = s ^ 18 := fun s => by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, pow_mul, sq_abs]
  simp only [h18] at h
  rw [h]
  have := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 18) (b := c) two_pos (by norm_num) hc
  simp only [Real.rpow_two, show (18 : ℝ) = ((18 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast] at this
  rw [this]
  have hG : Real.Gamma (19 / 2) = 34459425 / 512 * √π := by
    have := Real.Gamma_nat_add_half 9
    norm_num [Nat.doubleFactorial] at this
    rw [this]
    ring
  have hE : c ^ (-(((18 : ℕ) : ℝ) + 1) / 2) = (c ^ (1 / 2 : ℝ))⁻¹ / c ^ 9 := by
    rw [show -(((18 : ℕ) : ℝ) + 1) / 2 = -(9 + 1 / 2 : ℝ) by norm_num, Real.rpow_neg hc.le,
      Real.rpow_add hc, show (9 : ℝ) = ((9 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    field_simp
  have hS : √(π / c) = √π / c ^ (1 / 2 : ℝ) := by
    rw [Real.sqrt_div Real.pi_pos.le, Real.sqrt_eq_rpow c]
  rw [show (((18 : ℕ) : ℝ) + 1) / 2 = 19 / 2 by norm_num, hG, hE, hS]
  field_simp

/-! ### The fourth-order saddle estimate -/

/-- **Fourth-order Gaussian estimate** for `J₀(w) = ∫ exp(-w s² - i s³/3) ds`, `ρ = Re w > 0`:
`‖J₀ - (π/w)^{1/2} (1 - 5/(48 w³) + 385/(4608 w⁶))‖ ≤ (34459425/268738560) √(π/ρ)/ρ⁹`. -/
theorem norm_saddleJ0_fourth_le {w : ℂ} (hw : 0 < w.re) :
    ‖saddleJ0 w - (π / w) ^ (1 / 2 : ℂ) * (1 - 5 / (48 * w ^ 3) + 385 / (4608 * w ^ 6))‖ ≤
      34459425 / 268738560 * (√(π / w.re) / w.re ^ 9) := by
  have hw0 : w ≠ 0 := fun h => by simp [h] at hw
  set D : ℝ → ℂ := fun s => saddlePhase s -
    (1 - I * (s : ℂ) ^ 3 / 3 - (s : ℂ) ^ 6 / 18 + I * (s : ℂ) ^ 9 / 162 +
      (s : ℂ) ^ 12 / 1944 - I * (s : ℂ) ^ 15 / 29160) with hD
  have hDb : ∀ s, ‖D s‖ ≤ 1 / 524880 * s ^ 18 := fun s => by
    have := norm_saddlePhase_sub_poly6_le s
    simpa [hD, div_eq_inv_mul] using this
  have hDc : Continuous D := by simp only [hD, saddlePhase]; fun_prop
  have iG := integrable_pow_cexp_gauss hw 0
  have i3 := integrable_pow_cexp_gauss hw 3
  have i6 := integrable_pow_cexp_gauss hw 6
  have i9 := integrable_pow_cexp_gauss hw 9
  have i12 := integrable_pow_cexp_gauss hw 12
  have i15 := integrable_pow_cexp_gauss hw 15
  simp only [pow_zero, one_mul] at iG
  have h18 : ∀ s : ℝ, |s| ^ 18 = s ^ 18 := fun s => by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, pow_mul, sq_abs]
  have iDG : Integrable (fun s : ℝ => D s * saddleGauss w s) :=
    integrable_gauss_mul_of_le hw hDc 18 (1 / 524880) (fun s => by
      rw [h18]; exact hDb s)
  have hsplit : ∀ s : ℝ, saddlePhase s * saddleGauss w s =
      cexp (-w * (s : ℂ) ^ 2) - I / 3 * ((s : ℂ) ^ 3 * cexp (-w * (s : ℂ) ^ 2)) -
        1 / 18 * ((s : ℂ) ^ 6 * cexp (-w * (s : ℂ) ^ 2)) +
        I / 162 * ((s : ℂ) ^ 9 * cexp (-w * (s : ℂ) ^ 2)) +
        1 / 1944 * ((s : ℂ) ^ 12 * cexp (-w * (s : ℂ) ^ 2)) -
        I / 29160 * ((s : ℂ) ^ 15 * cexp (-w * (s : ℂ) ^ 2)) + D s * saddleGauss w s := by
    intro s; simp only [hD, saddleGauss]; ring
  have hodd : ∀ k : ℕ, Odd k → ∫ s : ℝ, (s : ℂ) ^ k * cexp (-w * (s : ℂ) ^ 2) = 0 := by
    intro k hk
    refine integral_eq_zero_of_odd fun s => ?_
    push_cast
    rw [neg_pow, hk.neg_one_pow]
    ring_nf
  have hJ : saddleJ0 w - (π / w) ^ (1 / 2 : ℂ) * (1 - 5 / (48 * w ^ 3) + 385 / (4608 * w ^ 6)) =
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
    have iE : Integrable (fun s : ℝ => cexp (-w * (s : ℂ) ^ 2) -
        I / 3 * ((s : ℂ) ^ 3 * cexp (-w * (s : ℂ) ^ 2)) -
        1 / 18 * ((s : ℂ) ^ 6 * cexp (-w * (s : ℂ) ^ 2)) +
        I / 162 * ((s : ℂ) ^ 9 * cexp (-w * (s : ℂ) ^ 2)) +
        1 / 1944 * ((s : ℂ) ^ 12 * cexp (-w * (s : ℂ) ^ 2))) := iC.add (i12.const_mul (1 / 1944))
    have iF : Integrable (fun s : ℝ => cexp (-w * (s : ℂ) ^ 2) -
        I / 3 * ((s : ℂ) ^ 3 * cexp (-w * (s : ℂ) ^ 2)) -
        1 / 18 * ((s : ℂ) ^ 6 * cexp (-w * (s : ℂ) ^ 2)) +
        I / 162 * ((s : ℂ) ^ 9 * cexp (-w * (s : ℂ) ^ 2)) +
        1 / 1944 * ((s : ℂ) ^ 12 * cexp (-w * (s : ℂ) ^ 2)) -
        I / 29160 * ((s : ℂ) ^ 15 * cexp (-w * (s : ℂ) ^ 2))) := iE.sub (i15.const_mul (I / 29160))
    rw [integral_add iF iDG, integral_sub iE (i15.const_mul (I / 29160)),
      integral_add iC (i12.const_mul (1 / 1944)), integral_add iB (i9.const_mul (I / 162)),
      integral_sub iA (i6.const_mul (1 / 18)), integral_sub iG (i3.const_mul (I / 3)),
      integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
      hodd 3 (by decide), hodd 9 (by decide), hodd 15 (by decide), integral_sixth_gauss_complex hw,
      airySO_integral_twelfth_gauss_complex hw, integral_gaussian_complex hw]
    field_simp
    ring
  rw [hJ]
  have i18 : Integrable (fun s : ℝ => 1 / 524880 * (s ^ 18 * Real.exp (-w.re * s ^ 2))) := by
    have := (integrable_abs_pow_gauss hw 18).const_mul (1 / 524880)
    simpa [h18] using this
  refine (norm_integral_le_of_norm_le i18 (Filter.Eventually.of_forall fun s => ?_)).trans ?_
  · rw [norm_mul, norm_saddleGauss]
    have := mul_le_mul_of_nonneg_right (hDb s) (Real.exp_pos (-w.re * s ^ 2)).le
    simpa [mul_assoc] using this
  · rw [integral_const_mul, airySO_integral_eighteenth_gauss hw]
    apply le_of_eq
    ring

/-- **Fourth-order saddle estimate for `Ai(w²)`**, `Re w > 0`:
`‖Ai(w²) - (e^{-(2/3)w³}/2π) (π/w)^{1/2} (1 - 5/(48 w³) + 385/(4608 w⁶))‖
  ≤ (1/2π) ‖e^{-(2/3)w³}‖ (34459425/268738560) √(π/ρ)/ρ⁹`. -/
theorem norm_airyAiC_sq_fourth_le {w : ℂ} (hw : 0 < w.re) :
    ‖airyAiC (w ^ 2) - (1 / (2 * (π : ℂ))) * cexp (-(2 / 3) * w ^ 3) *
        ((π / w) ^ (1 / 2 : ℂ) * (1 - 5 / (48 * w ^ 3) + 385 / (4608 * w ^ 6)))‖ ≤
      1 / (2 * π) * ‖cexp (-(2 / 3) * w ^ 3)‖ * (34459425 / 268738560 * (√(π / w.re) / w.re ^ 9)) := by
  have e : airyAiC (w ^ 2) - (1 / (2 * (π : ℂ))) * cexp (-(2 / 3) * w ^ 3) *
        ((π / w) ^ (1 / 2 : ℂ) * (1 - 5 / (48 * w ^ 3) + 385 / (4608 * w ^ 6))) =
      (1 / (2 * (π : ℂ))) * cexp (-(2 / 3) * w ^ 3) *
        (saddleJ0 w - (π / w) ^ (1 / 2 : ℂ) * (1 - 5 / (48 * w ^ 3) + 385 / (4608 * w ^ 6))) := by
    rw [airyAiC_sq_eq hw]; ring
  rw [e, norm_mul, norm_mul]
  have h1 : ‖(1 / (2 * (π : ℂ)))‖ = 1 / (2 * π) := by
    rw [norm_div, norm_one, norm_mul]; simp [abs_of_pos Real.pi_pos]
  rw [h1]
  exact mul_le_mul_of_nonneg_left (norm_saddleJ0_fourth_le hw) (by positivity)

/-- info: 'FormalResearch.Special.airySO_taylor_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airySO_taylor_le

/-- info: 'FormalResearch.Special.norm_saddleJ0_fourth_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.norm_saddleJ0_fourth_le

/-- info: 'FormalResearch.Special.norm_airyAiC_sq_fourth_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.norm_airyAiC_sq_fourth_le

end FormalResearch.Special
