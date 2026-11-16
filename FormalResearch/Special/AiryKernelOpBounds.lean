module

public import FormalResearch.Special.AiryKernelOpFormula

/-!
# Diagonal of the Airy kernel: monotonicity, bounds, and the closed forms of its integrals

Write `K(x) := K(x,x) = Ai'(x)² - x Ai(x)² = ∫_x^∞ Ai²` (`airyKer x x`, `airyKer_diag_nonneg`).

* `hasDerivAt_airyKer_diag`, `antitone_airyKer_diag`: `K' = -Ai² ≤ 0`.
* `airyKer_diag_le_sq`: for `x > 0`, `K(x) ≤ Ai'(x)² ≤ ((1/(2π))(√π x^{1/4} + x^{-1/2}) e^{-(2/3)x^{3/2}})²`
  (super-exponential decay on the forbidden side).
* `airyKer_diag_le`: **elementary growth bound** `K(x) ≤ C (1 + max(-x, 0))` for all real `x`, with the explicit
  constant `C = K(-1) = Ai(-1)² + Ai'(-1)²`.  Proof: for `x < 0` the quantity `Ai² + Ai'²/|x| = K(x)/|x|` is
  nondecreasing in `x` (derivative `Ai'²/x²`), so `K(x) ≤ |x| K(-1)` for `x ≤ -1`.
* `integral_Ioi_airyKer_diag`: **`N_Ai(u) := ∫_u^∞ K(s,s) ds = (2u²Ai(u)² - 2u Ai'(u)² - Ai(u)Ai'(u))/3`**
  (`airyN`), by differentiating the right-hand side (`Ai'' = x Ai`) and the decay of `Ai, Ai'` at `+∞`.
* `integral_Ioi_airyAi'_sq`: `∫_u^∞ Ai'² = (u²Ai(u)² - u Ai'(u)² - 2Ai(u)Ai'(u))/3`.
* `airyN_le`, `integral_Ioi_airyAi'_sq_le`: both are `≤ C' (1 + max(-u,0))²` for all real `u`.

The sharp bounds `K(x) ≤ C(1+x_-)^{1/2}` and `∫_u^∞ Ai'² ≤ C(1+u_-)^{3/2}` are proved in
`AiryKernelOpSharp` from the complex envelope; the exponents here are `1` and `2`, from the energy identity
alone.
-/

@[expose] public section

open Filter Topology MeasureTheory Set
open scoped Real

namespace FormalResearch.Special

/-! ### Decay of `t^n Ai²` and `t^n Ai'²` -/

lemma airyAi_sq_le {t : ℝ} (ht : 0 < t) :
    airyAi t ^ 2 ≤ (1 / (2 * √π)) ^ 2 * (t ^ (-(1 / 2) : ℝ) * Real.exp (-(4 / 3) * t ^ (3 / 2 : ℝ))) := by
  have h := airyAi_abs_le ht
  have h2 : airyAi t ^ 2 ≤ (1 / (2 * √π) * t ^ (-(1 / 4) : ℝ) *
      Real.exp (-(2 / 3) * t ^ (3 / 2 : ℝ))) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  refine h2.trans (le_of_eq ?_)
  have ha : t ^ (-(1 / 4) : ℝ) * t ^ (-(1 / 4) : ℝ) = t ^ (-(1 / 2) : ℝ) := by
    rw [← Real.rpow_add ht]; norm_num
  have he : Real.exp (-(2 / 3) * t ^ (3 / 2 : ℝ)) * Real.exp (-(2 / 3) * t ^ (3 / 2 : ℝ)) =
      Real.exp (-(4 / 3) * t ^ (3 / 2 : ℝ)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [← ha, ← he]; ring

lemma airyAi'_sq_le {t : ℝ} (ht : 0 < t) :
    airyAi' t ^ 2 ≤ (1 / (2 * π)) ^ 2 * 2 * (π * t ^ (1 / 2 : ℝ) + t ^ (-1 : ℝ)) *
      Real.exp (-(4 / 3) * t ^ (3 / 2 : ℝ)) := by
  have h := airyAi'_abs_le ht
  have h2 : airyAi' t ^ 2 ≤ (1 / (2 * π) * (√π * t ^ (1 / 4 : ℝ) + t ^ (-(1 / 2) : ℝ)) *
      Real.exp (-(2 / 3) * t ^ (3 / 2 : ℝ))) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  refine h2.trans ?_
  have ha : t ^ (1 / 4 : ℝ) * t ^ (1 / 4 : ℝ) = t ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add ht]; norm_num
  have hb : t ^ (-(1 / 2) : ℝ) * t ^ (-(1 / 2) : ℝ) = t ^ (-1 : ℝ) := by
    rw [← Real.rpow_add ht]; norm_num
  have he : Real.exp (-(2 / 3) * t ^ (3 / 2 : ℝ)) * Real.exp (-(2 / 3) * t ^ (3 / 2 : ℝ)) =
      Real.exp (-(4 / 3) * t ^ (3 / 2 : ℝ)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hs : √π * √π = π := Real.mul_self_sqrt Real.pi_pos.le
  have hE : 0 ≤ Real.exp (-(4 / 3) * t ^ (3 / 2 : ℝ)) := (Real.exp_pos _).le
  have hc : 0 ≤ (1 / (2 * π)) ^ 2 := by positivity
  have key : (√π * t ^ (1 / 4 : ℝ) + t ^ (-(1 / 2) : ℝ)) ^ 2 ≤
      2 * (π * t ^ (1 / 2 : ℝ) + t ^ (-1 : ℝ)) := by
    have hπ : π * t ^ (1 / 2 : ℝ) = (√π * t ^ (1 / 4 : ℝ)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt Real.pi_pos.le, sq (t ^ (1 / 4 : ℝ)), ha]
    have hb2 : t ^ (-1 : ℝ) = (t ^ (-(1 / 2) : ℝ)) ^ 2 := by rw [sq, hb]
    rw [hπ, hb2]
    nlinarith [sq_nonneg (√π * t ^ (1 / 4 : ℝ) - t ^ (-(1 / 2) : ℝ))]
  calc (1 / (2 * π) * (√π * t ^ (1 / 4 : ℝ) + t ^ (-(1 / 2) : ℝ)) *
        Real.exp (-(2 / 3) * t ^ (3 / 2 : ℝ))) ^ 2
      = (1 / (2 * π)) ^ 2 * (√π * t ^ (1 / 4 : ℝ) + t ^ (-(1 / 2) : ℝ)) ^ 2 *
        (Real.exp (-(2 / 3) * t ^ (3 / 2 : ℝ)) * Real.exp (-(2 / 3) * t ^ (3 / 2 : ℝ))) := by ring
    _ = (1 / (2 * π)) ^ 2 * (√π * t ^ (1 / 4 : ℝ) + t ^ (-(1 / 2) : ℝ)) ^ 2 *
        Real.exp (-(4 / 3) * t ^ (3 / 2 : ℝ)) := by rw [he]
    _ ≤ (1 / (2 * π)) ^ 2 * (2 * (π * t ^ (1 / 2 : ℝ) + t ^ (-1 : ℝ))) *
        Real.exp (-(4 / 3) * t ^ (3 / 2 : ℝ)) := by
        gcongr
    _ = _ := by ring

lemma tendsto_pow_mul_airyAi_sq (n : ℕ) :
    Tendsto (fun t : ℝ => t ^ n * airyAi t ^ 2) atTop (𝓝 0) := by
  have hg := (tendsto_rpow_mul_exp_rpow ((n : ℝ) - 1 / 2) (b := 4 / 3) (by norm_num)).const_mul
    ((1 / (2 * √π)) ^ 2)
  rw [mul_zero] at hg
  refine squeeze_zero' ?_ ?_ hg
  · filter_upwards [eventually_gt_atTop 0] with t ht
    positivity
  · filter_upwards [eventually_gt_atTop 0] with t ht
    have h := mul_le_mul_of_nonneg_left (airyAi_sq_le ht) (pow_nonneg ht.le n)
    refine h.trans (le_of_eq ?_)
    have : t ^ ((n : ℝ) - 1 / 2) = t ^ n * t ^ (-(1 / 2) : ℝ) := by
      rw [sub_eq_add_neg, Real.rpow_add ht, Real.rpow_natCast]
    rw [this]; ring

lemma tendsto_pow_mul_airyAi'_sq (n : ℕ) :
    Tendsto (fun t : ℝ => t ^ n * airyAi' t ^ 2) atTop (𝓝 0) := by
  have h1 := tendsto_rpow_mul_exp_rpow ((n : ℝ) + 1 / 2) (b := 4 / 3) (by norm_num)
  have h2 := tendsto_rpow_mul_exp_rpow ((n : ℝ) - 1) (b := 4 / 3) (by norm_num)
  have hg := ((h1.const_mul π).add h2).const_mul ((1 / (2 * π)) ^ 2 * 2)
  simp only [mul_zero, add_zero] at hg
  refine squeeze_zero' ?_ ?_ hg
  · filter_upwards [eventually_gt_atTop 0] with t ht
    positivity
  · filter_upwards [eventually_gt_atTop 0] with t ht
    have h := mul_le_mul_of_nonneg_left (airyAi'_sq_le ht) (pow_nonneg ht.le n)
    refine h.trans (le_of_eq ?_)
    have e1 : t ^ ((n : ℝ) + 1 / 2) = t ^ n * t ^ (1 / 2 : ℝ) := by
      rw [Real.rpow_add ht, Real.rpow_natCast]
    have e2 : t ^ ((n : ℝ) - 1) = t ^ n * t ^ (-1 : ℝ) := by
      rw [sub_eq_add_neg, Real.rpow_add ht, Real.rpow_natCast]
    rw [e1, e2]; ring

/-! ### Derivative and monotonicity of the diagonal -/

lemma hasDerivAt_airyKer_diag (x : ℝ) :
    HasDerivAt (fun x => airyKer x x) (-(airyAi x ^ 2)) x := by
  have h := (isAirySol_airyAi.hasDerivAt_energy x).neg
  have e : (fun x => airyKer x x) = -(fun x => x * airyAi x ^ 2 - airyAi' x ^ 2) := by
    funext y
    simp only [Pi.neg_apply, airyKer_self]; ring
  rw [e]; exact h

lemma antitone_airyKer_diag : Antitone (fun x => airyKer x x) := by
  refine antitone_of_deriv_nonpos (fun x => (hasDerivAt_airyKer_diag x).differentiableAt) ?_
  intro x
  rw [(hasDerivAt_airyKer_diag x).deriv]
  exact neg_nonpos.mpr (sq_nonneg _)

/-- Forbidden-side decay: for `x > 0`, `K(x,x) ≤ Ai'(x)²`, hence
`K(x,x) ≤ ((1/(2π))(√π x^{1/4} + x^{-1/2}) e^{-(2/3) x^{3/2}})²`. -/
theorem airyKer_diag_le_sq {x : ℝ} (hx : 0 < x) :
    airyKer x x ≤ (1 / (2 * π) * (√π * x ^ (1 / 4 : ℝ) + x ^ (-(1 / 2) : ℝ)) *
      Real.exp (-(2 / 3) * x ^ (3 / 2 : ℝ))) ^ 2 := by
  have h := airyAi'_abs_le hx
  have h2 := pow_le_pow_left₀ (abs_nonneg _) h 2
  rw [sq_abs] at h2
  refine le_trans ?_ h2
  rw [airyKer_self]
  nlinarith [mul_nonneg hx.le (sq_nonneg (airyAi x))]

/-! ### The growth bound `K(x,x) ≤ C(1 + x_-)` -/

/-- `Φ(x) = Ai(x)² + Ai'(x)²/(-x)` has derivative `Ai'(x)²/x²` for `x ≠ 0`. -/
lemma hasDerivAt_airyPhi {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun x => airyAi x ^ 2 + airyAi' x ^ 2 / (-x)) (airyAi' x ^ 2 / x ^ 2) x := by
  have h1 := (hasDerivAt_airyAi x).pow 2
  have h2 := ((hasDerivAt_airyAi' x).pow 2).div (hasDerivAt_neg x) (neg_ne_zero.mpr hx)
  refine (h1.add h2).congr_deriv ?_
  simp only [Pi.pow_apply]
  field_simp
  ring

lemma airyPhi_mono : MonotoneOn (fun x => airyAi x ^ 2 + airyAi' x ^ 2 / (-x)) (Iic (-1)) := by
  have hd : ∀ x ∈ Iic (-1 : ℝ), HasDerivAt (fun x => airyAi x ^ 2 + airyAi' x ^ 2 / (-x))
      (airyAi' x ^ 2 / x ^ 2) x := fun x hx => hasDerivAt_airyPhi (by
    have : x ≤ -1 := hx
    exact (by linarith : x < 0).ne)
  refine monotoneOn_of_deriv_nonneg (convex_Iic (-1))
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt) ?_
  intro x hx
  rw [interior_Iic] at hx
  rw [(hd x (le_of_lt hx)).deriv]
  positivity

lemma airyKer_diag_eq_mul {x : ℝ} (hx : x ≠ 0) :
    airyKer x x = (-x) * (airyAi x ^ 2 + airyAi' x ^ 2 / (-x)) := by
  rw [airyKer_self]
  field_simp
  ring

/-- **Elementary growth bound**: `K(x,x) ≤ K(-1,-1) (1 + max(-x, 0))` for every real `x`
(exponent `1`; the sharp exponent `1/2` needs the oscillatory asymptotics). -/
theorem airyKer_diag_le (x : ℝ) :
    airyKer x x ≤ airyKer (-1) (-1) * (1 + max (-x) 0) := by
  have hC := airyKer_diag_nonneg (-1)
  by_cases hx : -1 ≤ x
  · have h1 : airyKer x x ≤ airyKer (-1) (-1) := antitone_airyKer_diag hx
    have : 0 ≤ max (-x) 0 := le_max_right _ _
    nlinarith
  · push Not at hx
    have hx0 : x ≠ 0 := by intro h; rw [h] at hx; norm_num at hx
    have h1 := airyPhi_mono (show x ∈ Iic (-1 : ℝ) from hx.le) (show (-1 : ℝ) ∈ Iic (-1 : ℝ) from le_rfl)
      hx.le
    simp only at h1
    have e1 := airyKer_diag_eq_mul hx0
    have e2 : airyKer (-1) (-1) = (-(-1 : ℝ)) * (airyAi (-1) ^ 2 + airyAi' (-1) ^ 2 / (-(-1 : ℝ))) :=
      airyKer_diag_eq_mul (by norm_num)
    have e3 : airyKer (-1) (-1) = airyAi (-1) ^ 2 + airyAi' (-1) ^ 2 / (-(-1 : ℝ)) := by
      rw [e2]; ring
    rw [e1]
    have hmax : max (-x) 0 = -x := max_eq_left (by linarith)
    rw [hmax]
    rw [← e3] at h1
    nlinarith

/-! ### Closed forms for `∫_u^∞ K(s,s) ds` and `∫_u^∞ Ai'²` -/

/-- `N_Ai(u) = (2u²Ai(u)² - 2uAi'(u)² - Ai(u)Ai'(u))/3`, the Airy mean counting function
(`= ∫_u^∞ K(s,s) ds`, `integral_Ioi_airyKer_diag`). -/
noncomputable def airyN (u : ℝ) : ℝ :=
  (2 * u ^ 2 * airyAi u ^ 2 - 2 * u * airyAi' u ^ 2 - airyAi u * airyAi' u) / 3

/-- `R(u) = (u²Ai(u)² - uAi'(u)² - 2Ai(u)Ai'(u))/3`, `= ∫_u^∞ Ai'²`. -/
noncomputable def airyR (u : ℝ) : ℝ :=
  (u ^ 2 * airyAi u ^ 2 - u * airyAi' u ^ 2 - 2 * airyAi u * airyAi' u) / 3

lemma hasDerivAt_airyN (u : ℝ) : HasDerivAt airyN (-(airyKer u u)) u := by
  have hA := hasDerivAt_airyAi u
  have hB := hasDerivAt_airyAi' u
  have h : HasDerivAt (fun u => (2 * (u * u) * (airyAi u * airyAi u) -
      2 * u * (airyAi' u * airyAi' u) - airyAi u * airyAi' u) / 3) _ u :=
    ((((((hasDerivAt_id' u).mul (hasDerivAt_id' u)).const_mul 2).mul (hA.mul hA)).sub
      (((hasDerivAt_id' u).const_mul 2).mul (hB.mul hB))).sub (hA.mul hB)).div_const 3
  convert h using 1
  · funext v; unfold airyN; ring
  · simp only [Pi.mul_apply, airyKer_self]; ring

lemma hasDerivAt_airyR (u : ℝ) : HasDerivAt airyR (-(airyAi' u ^ 2)) u := by
  have hA := hasDerivAt_airyAi u
  have hB := hasDerivAt_airyAi' u
  have h : HasDerivAt (fun u => ((u * u) * (airyAi u * airyAi u) -
      u * (airyAi' u * airyAi' u) - 2 * airyAi u * airyAi' u) / 3) _ u :=
    ((((((hasDerivAt_id' u).mul (hasDerivAt_id' u))).mul (hA.mul hA)).sub
      ((hasDerivAt_id' u).mul (hB.mul hB))).sub ((hA.const_mul 2).mul hB)).div_const 3
  convert h using 1
  · funext v; unfold airyR; ring
  · simp only [Pi.mul_apply]; ring

lemma tendsto_airyN : Tendsto airyN atTop (𝓝 0) := by
  have h1 := tendsto_pow_mul_airyAi_sq 2
  have h2 := tendsto_pow_mul_airyAi'_sq 1
  have h3 := tendsto_airyAi.mul tendsto_airyAi'
  have h := (((h1.const_mul 2).sub (h2.const_mul 2)).sub h3).div_const 3
  simp only [mul_zero, sub_zero, zero_div] at h
  refine h.congr fun u => ?_
  unfold airyN; ring

lemma tendsto_airyR : Tendsto airyR atTop (𝓝 0) := by
  have h1 := tendsto_pow_mul_airyAi_sq 2
  have h2 := tendsto_pow_mul_airyAi'_sq 1
  have h3 := tendsto_airyAi.mul tendsto_airyAi'
  have h := ((h1.sub h2).sub (h3.const_mul 2)).div_const 3
  simp only [mul_zero, sub_zero, zero_div] at h
  refine h.congr fun u => ?_
  unfold airyR; ring

lemma hasDerivAt_neg_airyN (x : ℝ) : HasDerivAt (fun s => -airyN s) (airyKer x x) x := by
  have h := (hasDerivAt_airyN x).neg
  rw [neg_neg] at h
  exact h

lemma hasDerivAt_neg_airyR (x : ℝ) : HasDerivAt (fun s => -airyR s) (airyAi' x ^ 2) x := by
  have h := (hasDerivAt_airyR x).neg
  rw [neg_neg] at h
  exact h

/-- **`N_Ai(u) = ∫_u^∞ K(s,s) ds = (2u²Ai(u)² - 2uAi'(u)² - Ai(u)Ai'(u))/3`.** -/
theorem integral_Ioi_airyKer_diag (u : ℝ) : ∫ s in Ioi u, airyKer s s = airyN u := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg' (a := u) (g := fun s => -airyN s)
    (g' := fun s => airyKer s s) (l := 0)
    (fun x _ => hasDerivAt_neg_airyN x) (fun x _ => airyKer_diag_nonneg x)
    (by simpa using tendsto_airyN.neg)
  rw [h]; simp

theorem integrableOn_Ioi_airyKer_diag (u : ℝ) : IntegrableOn (fun s => airyKer s s) (Ioi u) :=
  integrableOn_Ioi_deriv_of_nonneg' (a := u) (g := fun s => -airyN s)
    (g' := fun s => airyKer s s) (l := 0)
    (fun x _ => hasDerivAt_neg_airyN x) (fun x _ => airyKer_diag_nonneg x)
    (by simpa using tendsto_airyN.neg)

/-- **`∫_u^∞ Ai'(s)² ds = (u²Ai(u)² - uAi'(u)² - 2Ai(u)Ai'(u))/3`.** -/
theorem integral_Ioi_airyAi'_sq (u : ℝ) : ∫ s in Ioi u, airyAi' s ^ 2 = airyR u := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg' (a := u) (g := fun s => -airyR s)
    (g' := fun s => airyAi' s ^ 2) (l := 0)
    (fun x _ => hasDerivAt_neg_airyR x) (fun x _ => sq_nonneg _)
    (by simpa using tendsto_airyR.neg)
  rw [h]; simp

theorem integrableOn_Ioi_airyAi'_sq (u : ℝ) : IntegrableOn (fun s => airyAi' s ^ 2) (Ioi u) :=
  integrableOn_Ioi_deriv_of_nonneg' (a := u) (g := fun s => -airyR s)
    (g' := fun s => airyAi' s ^ 2) (l := 0)
    (fun x _ => hasDerivAt_neg_airyR x) (fun x _ => sq_nonneg _)
    (by simpa using tendsto_airyR.neg)

lemma airyN_nonneg (u : ℝ) : 0 ≤ airyN u := by
  rw [← integral_Ioi_airyKer_diag]
  exact setIntegral_nonneg measurableSet_Ioi fun s _ => airyKer_diag_nonneg s

lemma airyR_nonneg (u : ℝ) : 0 ≤ airyR u := by
  rw [← integral_Ioi_airyAi'_sq]
  exact setIntegral_nonneg measurableSet_Ioi fun s _ => sq_nonneg _

/-- A function whose derivative is at least `-C(1-u)` on `u ≤ 0` is at most `F(0) + C(-u + u²/2)` there. -/
lemma le_of_hasDerivAt_ge {F F' : ℝ → ℝ} {C : ℝ} (hF : ∀ u, HasDerivAt F (F' u) u)
    (h : ∀ u ≤ 0, -(C * (1 - u)) ≤ F' u) {u : ℝ} (hu : u ≤ 0) :
    F u ≤ F 0 + C * (-u + u ^ 2 / 2) := by
  have hd : ∀ u, HasDerivAt (fun u => F u - C * (-u + u ^ 2 / 2)) (F' u + C * (1 - u)) u := by
    intro u
    have h2 : HasDerivAt (fun u : ℝ => C * (-u + u ^ 2 / 2)) (C * (-1 + u)) u := by
      have := (((hasDerivAt_id' u).neg).add ((hasDerivAt_pow 2 u).div_const 2)).const_mul C
      convert this using 1
      simp
    convert (hF u).sub h2 using 1
    ring
  have hm : MonotoneOn (fun u => F u - C * (-u + u ^ 2 / 2)) (Iic 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Iic 0)
      (fun x _ => (hd x).continuousAt.continuousWithinAt)
      (fun x _ => (hd x).differentiableAt.differentiableWithinAt) ?_
    intro x hx
    rw [interior_Iic] at hx
    rw [(hd x).deriv]
    linarith [h x (le_of_lt hx)]
  have := hm (show u ∈ Iic (0 : ℝ) from hu) (show (0 : ℝ) ∈ Iic (0 : ℝ) from le_rfl) hu
  simp at this
  linarith

/-- `N_Ai(u) ≤ (N_Ai(0) + K(-1,-1)) (1 + u_-)²` for every real `u`. -/
theorem airyN_le (u : ℝ) :
    airyN u ≤ (airyN 0 + airyKer (-1) (-1)) * (1 + max (-u) 0) ^ 2 := by
  have hC := airyKer_diag_nonneg (-1)
  have h0 := airyN_nonneg 0
  by_cases hu : 0 ≤ u
  · have : airyN u ≤ airyN 0 := by
      have hanti : Antitone airyN := antitone_of_deriv_nonpos
        (fun x => (hasDerivAt_airyN x).differentiableAt) (fun x => by
          rw [(hasDerivAt_airyN x).deriv]; exact neg_nonpos.mpr (airyKer_diag_nonneg x))
      exact hanti hu
    have hm : max (-u) 0 = 0 := max_eq_right (by linarith)
    rw [hm]; nlinarith
  · push Not at hu
    have h := le_of_hasDerivAt_ge (F := airyN) (F' := fun u => -(airyKer u u))
      (C := airyKer (-1) (-1)) hasDerivAt_airyN
      (fun v hv => by
        have := airyKer_diag_le v
        have hm : max (-v) 0 = -v := max_eq_left (by linarith)
        rw [hm] at this
        linarith) hu.le
    have hm : max (-u) 0 = -u := max_eq_left (by linarith)
    rw [hm]
    nlinarith [sq_nonneg u, mul_nonneg hC (sq_nonneg u), mul_nonneg h0 (sq_nonneg u),
      mul_nonneg h0 (neg_nonneg.mpr hu.le), mul_nonneg hC (neg_nonneg.mpr hu.le)]

/-- `∫_u^∞ Ai'² ≤ (R(0) + K(-1,-1)) (1 + u_-)²`, where `R(0) = ∫_0^∞ Ai'²`
(exponent `2`; the sharp exponent `3/2` needs the oscillatory asymptotics). -/
theorem integral_Ioi_airyAi'_sq_le (u : ℝ) :
    ∫ s in Ioi u, airyAi' s ^ 2 ≤ (airyR 0 + airyKer (-1) (-1)) * (1 + max (-u) 0) ^ 2 := by
  rw [integral_Ioi_airyAi'_sq]
  have hC := airyKer_diag_nonneg (-1)
  have h0 := airyR_nonneg 0
  by_cases hu : 0 ≤ u
  · have : airyR u ≤ airyR 0 := by
      have hanti : Antitone airyR := antitone_of_deriv_nonpos
        (fun x => (hasDerivAt_airyR x).differentiableAt) (fun x => by
          rw [(hasDerivAt_airyR x).deriv]; exact neg_nonpos.mpr (sq_nonneg _))
      exact hanti hu
    have hm : max (-u) 0 = 0 := max_eq_right (by linarith)
    rw [hm]; nlinarith
  · push Not at hu
    have h := le_of_hasDerivAt_ge (F := airyR) (F' := fun u => -(airyAi' u ^ 2))
      (C := airyKer (-1) (-1)) hasDerivAt_airyR
      (fun v hv => by
        have h1 := airyKer_diag_le v
        have hm : max (-v) 0 = -v := max_eq_left (by linarith)
        rw [hm] at h1
        rw [airyKer_self] at h1
        nlinarith [mul_nonneg (neg_nonneg.mpr hv) (sq_nonneg (airyAi v))]) hu.le
    have hm : max (-u) 0 = -u := max_eq_left (by linarith)
    rw [hm]
    nlinarith [sq_nonneg u, mul_nonneg hC (sq_nonneg u), mul_nonneg h0 (sq_nonneg u),
      mul_nonneg h0 (neg_nonneg.mpr hu.le), mul_nonneg hC (neg_nonneg.mpr hu.le)]

/-- info: 'FormalResearch.Special.airyKer_diag_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyKer_diag_le

/-- info: 'FormalResearch.Special.airyKer_diag_le_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyKer_diag_le_sq

/-- info: 'FormalResearch.Special.integral_Ioi_airyKer_diag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.integral_Ioi_airyKer_diag

/-- info: 'FormalResearch.Special.integral_Ioi_airyAi'_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.integral_Ioi_airyAi'_sq

/-- info: 'FormalResearch.Special.airyN_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyN_le

/-- info: 'FormalResearch.Special.integral_Ioi_airyAi'_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.integral_Ioi_airyAi'_sq_le

end FormalResearch.Special
