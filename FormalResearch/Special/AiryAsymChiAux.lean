module

public import FormalResearch.Special.AiryAsymSaddle

/-!
# Auxiliary estimates for the third-order saddle expansion of `Ai(w²)`

* `norm_le_of_hasDerivAt_bound`: a one-variable integration lemma (`f(0) = 0`, `‖f'(t)‖ ≤ |t|^n/n!`
  implies `‖f(x)‖ ≤ |x|^{n+1}/(n+1)!` for all real `x`);
* `norm_exp_I_mul_sub_cubic_le`: `‖e^{ix} - 1 - ix - (ix)²/2 - (ix)³/6‖ ≤ x⁴/24` (the sharp Taylor bound of order four);
* `integral_pow_gauss_succ` and `integral_sixth_gauss_complex`: the complex Gaussian moments
  `∫ s^{k+2} e^{-w s²} ds = ((k+1)/(2w)) ∫ s^k e^{-w s²} ds` (`Re w > 0`) and `∫ s⁶ e^{-w s²} = (15/(8w³)) (π/w)^{1/2}`,
  by integration by parts.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.Special

/-- One integration step of the Taylor bounds: `f(0) = 0` and `‖f'(t)‖ ≤ |t|^n / n!` for all `t` give
`‖f(x)‖ ≤ |x|^{n+1} / (n+1)!`. -/
lemma norm_le_of_hasDerivAt_bound (f g : ℝ → ℂ) (n : ℕ) (hf : ∀ t, HasDerivAt f (g t) t)
    (h0 : f 0 = 0) (hg : ∀ t, ‖g t‖ ≤ |t| ^ n / (n.factorial : ℝ)) (x : ℝ) :
    ‖f x‖ ≤ |x| ^ (n + 1) / ((n + 1).factorial : ℝ) := by
  have hpos : ∀ (f g : ℝ → ℂ), (∀ t, HasDerivAt f (g t) t) → f 0 = 0 →
      (∀ t, ‖g t‖ ≤ |t| ^ n / (n.factorial : ℝ)) → ∀ x : ℝ, 0 ≤ x →
      ‖f x‖ ≤ |x| ^ (n + 1) / ((n + 1).factorial : ℝ) := by
    intro f g hf h0 hg x hx
    have hfac : ((n + 1).factorial : ℝ) = (n + 1) * n.factorial := by
      push_cast [Nat.factorial_succ]; ring
    have hfn : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
    have := image_norm_le_of_norm_deriv_right_le_deriv_boundary
      (f := f) (a := 0) (b := x) (f' := g)
      (fun t _ => (hf t).continuousAt.continuousWithinAt)
      (fun t _ => (hf t).hasDerivWithinAt) (B := fun t => t ^ (n + 1) / ((n + 1).factorial : ℝ))
      (B' := fun t => t ^ n / (n.factorial : ℝ))
      (by simp [h0]) (fun t => by
        have := (hasDerivAt_pow (n + 1) t).div_const (((n + 1).factorial : ℝ))
        convert this using 1
        rw [hfac]
        push_cast
        field_simp)
      (fun t ht => by
        have := hg t
        rwa [abs_of_nonneg ht.1] at this) ⟨hx, le_rfl⟩
    simpa [abs_of_nonneg hx] using this
  rcases le_total 0 x with hx | hx
  · exact hpos f g hf h0 hg x hx
  · have hf' : ∀ t, HasDerivAt (fun t => f (-t)) (-g (-t)) t := by
      intro t
      have := (hf (-t)).scomp t (hasDerivAt_neg t)
      convert this using 1
      · rfl
      · rw [neg_smul, one_smul]
    have := hpos (fun t => f (-t)) (fun t => -g (-t)) hf' (by simp [h0])
      (fun t => by simpa [abs_neg] using hg (-t)) (-x) (by linarith)
    simpa [abs_neg] using this

/-- Taylor remainder of order four: `‖e^{ix} - 1 - ix - (ix)²/2 - (ix)³/6‖ ≤ x⁴/24`. -/
lemma norm_exp_I_mul_sub_cubic_le (x : ℝ) :
    ‖cexp (I * (x : ℂ)) - 1 - I * (x : ℂ) - (I * (x : ℂ)) ^ 2 / 2 - (I * (x : ℂ)) ^ 3 / 6‖ ≤
      x ^ 4 / 24 := by
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => cexp (I * (t : ℂ))) (I * cexp (I * (t : ℂ))) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => I * (t : ℂ)) I t := by
      simpa using ((hasDerivAt_id t).ofReal_comp).const_mul I
    simpa [mul_comm] using h1.cexp
  have hp : ∀ (m : ℕ) (t : ℝ), HasDerivAt (fun t : ℝ => (I * (t : ℂ)) ^ m)
      (I * (m * (I * (t : ℂ)) ^ (m - 1))) t := by
    intro m t
    have h1 : HasDerivAt (fun t : ℝ => I * (t : ℂ)) I t := by
      simpa using ((hasDerivAt_id t).ofReal_comp).const_mul I
    have := h1.pow m
    convert this using 1
    ring
  -- step 0: `‖e^{it} - 1‖ ≤ |t|`
  have s1 : ∀ x : ℝ, ‖cexp (I * (x : ℂ)) - 1‖ ≤ |x| ^ 1 / ((1 : ℕ).factorial : ℝ) := by
    intro x
    have := norm_le_of_hasDerivAt_bound (fun t : ℝ => cexp (I * (t : ℂ)) - 1)
      (fun t => I * cexp (I * (t : ℂ))) 0 (fun t => (hd t).sub_const 1) (by simp)
      (fun t => by simp) x
    simpa using this
  have s2 : ∀ x : ℝ, ‖cexp (I * (x : ℂ)) - 1 - I * (x : ℂ)‖ ≤ |x| ^ 2 / ((2 : ℕ).factorial : ℝ) := by
    intro x
    have h1 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => cexp (I * (t : ℂ)) - 1 - I * (t : ℂ))
        (I * (cexp (I * (t : ℂ)) - 1)) t := by
      intro t
      have h2 : HasDerivAt (fun t : ℝ => I * (t : ℂ)) I t := by
        simpa using ((hasDerivAt_id t).ofReal_comp).const_mul I
      refine ((hd t).sub_const 1 |>.sub h2).congr_deriv ?_
      ring
    have := norm_le_of_hasDerivAt_bound _ _ 1 h1 (by simp)
      (fun t => by
        rw [norm_mul, Complex.norm_I, one_mul]
        simpa using s1 t) x
    simpa using this
  have s3 : ∀ x : ℝ, ‖cexp (I * (x : ℂ)) - 1 - I * (x : ℂ) - (I * (x : ℂ)) ^ 2 / 2‖ ≤
      |x| ^ 3 / ((3 : ℕ).factorial : ℝ) := by
    intro x
    have h1 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => cexp (I * (t : ℂ)) - 1 - I * (t : ℂ) -
        (I * (t : ℂ)) ^ 2 / 2) (I * (cexp (I * (t : ℂ)) - 1 - I * (t : ℂ))) t := by
      intro t
      have h2 : HasDerivAt (fun t : ℝ => I * (t : ℂ)) I t := by
        simpa using ((hasDerivAt_id t).ofReal_comp).const_mul I
      have h3 := (hp 2 t).div_const 2
      refine (((hd t).sub_const 1 |>.sub h2).sub h3).congr_deriv ?_
      simp only [Nat.cast_ofNat]
      ring_nf
    have := norm_le_of_hasDerivAt_bound _ _ 2 h1 (by simp)
      (fun t => by
        rw [norm_mul, Complex.norm_I, one_mul]
        simpa using s2 t) x
    simpa using this
  have := norm_le_of_hasDerivAt_bound
    (fun t : ℝ => cexp (I * (t : ℂ)) - 1 - I * (t : ℂ) - (I * (t : ℂ)) ^ 2 / 2 -
      (I * (t : ℂ)) ^ 3 / 6)
    (fun t => I * (cexp (I * (t : ℂ)) - 1 - I * (t : ℂ) - (I * (t : ℂ)) ^ 2 / 2)) 3
    (fun t => by
      have h2 : HasDerivAt (fun t : ℝ => I * (t : ℂ)) I t := by
        simpa using ((hasDerivAt_id t).ofReal_comp).const_mul I
      have h3 := (hp 2 t).div_const 2
      have h4 := (hp 3 t).div_const 6
      refine ((((hd t).sub_const 1 |>.sub h2).sub h3).sub h4).congr_deriv ?_
      simp only [Nat.cast_ofNat]
      ring_nf) (by simp)
    (fun t => by
      rw [norm_mul, Complex.norm_I, one_mul]
      simpa using s3 t) x
  have e : ((4 : ℕ).factorial : ℝ) = 24 := by norm_num [Nat.factorial]
  rw [e, show |x| ^ (3 + 1) = x ^ 4 from abs_pow_four x] at this
  exact this


lemma tendsto_abs_pow_gauss {ρ : ℝ} (hρ : 0 < ρ) (k : ℕ) :
    Tendsto (fun s : ℝ => |s| ^ k * Real.exp (-ρ * s ^ 2)) (cocompact ℝ) (𝓝 0) := by
  have h : Tendsto (fun x : ℝ => x ^ (k : ℝ) * Real.exp (-ρ * x ^ 2)) atTop (𝓝 0) :=
    ((rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg hρ (k : ℝ)).isBigO).trans_tendsto
      (Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by norm_num)))
  rw [cocompact_eq_atBot_atTop]
  refine Tendsto.sup ?_ ?_
  · have := h.comp tendsto_neg_atBot_atTop
    refine this.congr' ?_
    filter_upwards [eventually_le_atBot (0 : ℝ)] with s hs
    simp [Real.rpow_natCast, abs_of_nonpos hs]
  · refine h.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
    simp [Real.rpow_natCast, abs_of_nonneg hs]

lemma tendsto_pow_mul_cexp_gauss {w : ℂ} (hw : 0 < w.re) (k : ℕ) :
    Tendsto (fun s : ℝ => (s : ℂ) ^ k * cexp (-w * (s : ℂ) ^ 2)) (cocompact ℝ) (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine (tendsto_abs_pow_gauss hw k).congr (fun s => ?_)
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, norm_cexp_neg_mul_sq]


lemma integrable_pow_cexp_gauss {w : ℂ} (hw : 0 < w.re) (k : ℕ) :
    Integrable (fun s : ℝ => (s : ℂ) ^ k * cexp (-w * (s : ℂ) ^ 2)) := by
  have := integrable_gauss_mul_of_le hw (f := fun s : ℝ => (s : ℂ) ^ k) (by fun_prop) k 1
    (fun s => by simp)
  simpa [saddleGauss] using this

/-- Integration by parts for the complex Gaussian moments: `∫ s^{k+2} e^{-w s²} = ((k+1)/(2w)) ∫ s^k e^{-w s²}`. -/
lemma integral_pow_gauss_succ {w : ℂ} (hw : 0 < w.re) (k : ℕ) :
    ∫ s : ℝ, (s : ℂ) ^ (k + 2) * cexp (-w * (s : ℂ) ^ 2) =
      ((k + 1 : ℂ) / (2 * w)) * ∫ s : ℝ, (s : ℂ) ^ k * cexp (-w * (s : ℂ) ^ 2) := by
  have hw0 : w ≠ 0 := fun h => by simp [h] at hw
  have hd : ∀ s : ℝ, HasDerivAt (fun s : ℝ => (s : ℂ) ^ (k + 1) * cexp (-w * (s : ℂ) ^ 2))
      ((k + 1 : ℂ) * ((s : ℂ) ^ k * cexp (-w * (s : ℂ) ^ 2)) -
        2 * w * ((s : ℂ) ^ (k + 2) * cexp (-w * (s : ℂ) ^ 2))) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 s := (hasDerivAt_id s).ofReal_comp
    have h2 : HasDerivAt (fun s : ℝ => (s : ℂ) ^ (k + 1)) (((k + 1 : ℕ) : ℂ) * (s : ℂ) ^ k) s :=
      (hasDerivAt_pow (k + 1) (s : ℂ)).comp_ofReal
    have h3 : HasDerivAt (fun s : ℝ => -w * (s : ℂ) ^ 2) (-w * (2 * (s : ℂ))) s := by
      simpa using (h1.pow 2).const_mul (-w)
    have h4 := h3.cexp
    have := h2.mul h4
    refine this.congr_deriv ?_
    push_cast
    ring
  have i1 := (integrable_pow_cexp_gauss hw k).const_mul (k + 1 : ℂ)
  have i2 := (integrable_pow_cexp_gauss hw (k + 2)).const_mul (2 * w)
  have hint := i1.sub i2
  have h0 := integral_of_hasDerivAt_of_tendsto hd hint
    ((tendsto_pow_mul_cexp_gauss hw (k + 1)).mono_left
      (by rw [cocompact_eq_atBot_atTop]; exact le_sup_left))
    ((tendsto_pow_mul_cexp_gauss hw (k + 1)).mono_left
      (by rw [cocompact_eq_atBot_atTop]; exact le_sup_right))
  rw [sub_zero, integral_sub i1 i2, integral_const_mul, integral_const_mul] at h0
  have h2w : (2 * w) ≠ 0 := mul_ne_zero two_ne_zero hw0
  rw [div_mul_eq_mul_div, eq_div_iff h2w]
  linear_combination -h0

/-- `∫ s⁶ e^{-w s²} = (15/(8 w³)) (π/w)^{1/2}` for `Re w > 0`. -/
lemma integral_sixth_gauss_complex {w : ℂ} (hw : 0 < w.re) :
    ∫ s : ℝ, (s : ℂ) ^ 6 * cexp (-w * (s : ℂ) ^ 2) = 15 / (8 * w ^ 3) * (π / w) ^ (1 / 2 : ℂ) := by
  have hw0 : w ≠ 0 := fun h => by simp [h] at hw
  have e4 : ∫ s : ℝ, (s : ℂ) ^ 6 * cexp (-w * (s : ℂ) ^ 2) =
      (5 / (2 * w)) * ∫ s : ℝ, (s : ℂ) ^ 4 * cexp (-w * (s : ℂ) ^ 2) := by
    have h := integral_pow_gauss_succ hw 4
    norm_num at h ⊢
    exact h
  have e2 : ∫ s : ℝ, (s : ℂ) ^ 4 * cexp (-w * (s : ℂ) ^ 2) =
      (3 / (2 * w)) * ∫ s : ℝ, (s : ℂ) ^ 2 * cexp (-w * (s : ℂ) ^ 2) := by
    have h := integral_pow_gauss_succ hw 2
    norm_num at h ⊢
    exact h
  have e0 : ∫ s : ℝ, (s : ℂ) ^ 2 * cexp (-w * (s : ℂ) ^ 2) =
      (1 / (2 * w)) * ∫ s : ℝ, cexp (-w * (s : ℂ) ^ 2) := by
    have h := integral_pow_gauss_succ hw 0
    norm_num at h ⊢
    exact h
  rw [e4, e2, e0, integral_gaussian_complex hw]
  field_simp
  ring

/-- info: 'FormalResearch.Special.norm_exp_I_mul_sub_cubic_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.norm_exp_I_mul_sub_cubic_le

/-- info: 'FormalResearch.Special.integral_sixth_gauss_complex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.integral_sixth_gauss_complex

end FormalResearch.Special
