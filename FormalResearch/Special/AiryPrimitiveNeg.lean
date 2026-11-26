module

public import FormalResearch.Special.AiryIntegral
public import FormalResearch.Special.AiryKernelOpSharp

/-!
# Decay of the Airy primitives on the negative axis (phase-free)

`Bneg t = 2/3 - ∫_t^0 Ai` is `B(t) = ∫_{-∞}^t Ai` (improper; `tendsto_int_bot`: `∫_{-S}^t Ai → Bneg t`, from
`tendsto_integral_airyAi_bot_zero`).  From `Ai'' = x Ai` the function `F(x) = Ai'(x)/x + Ai(x)/x²` has derivative
`Ai - 2 Ai/x³` away from `0`, so for `-S ≤ t ≤ -1`
`∫_{-S}^t Ai = F(t) - F(-S) + 2 ∫_{-S}^t Ai/x³`, and with the envelope bounds `|Ai| ≤ 3 (1+|x|)^{-1/4}`,
`|Ai'| ≤ 5 (1+|x|)^{1/4}` (`AiryKernelOpSharp`) one gets, letting `S → ∞` (no oscillation is used),

* `Bneg_sub_Fk_le`: `|B(t) - F(t)| ≤ (8/3) |t|^{-9/4}`;
* **`Bneg_decay`**: `|B(t)| ≤ 16 |t|^{-3/4}` and `|t B(t) - Ai'(t)| ≤ 16 |t|^{-5/4}` for `t ≤ -1`.

All proved, constants explicit.
-/

@[expose] public section

open Set MeasureTheory intervalIntegral Filter Topology
open scoped Real

namespace FormalResearch.Special.AiryPrimNeg

/-- The antiderivative `F(x) = Ai'(x)/x + Ai(x)/x²` of `Ai - 2 Ai/x³` away from `0`. -/
noncomputable def Fk (x : ℝ) : ℝ := airyAi' x / x + airyAi x / x ^ 2

lemma hasDerivAt_Fk {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt Fk (airyAi x - 2 * airyAi x / x ^ 3) x := by
  have h1 := (hasDerivAt_airyAi' x).div (hasDerivAt_id x) hx
  have h2 := (hasDerivAt_airyAi x).div ((hasDerivAt_pow 2 x)) (pow_ne_zero 2 hx)
  have := h1.add h2
  unfold Fk
  refine this.congr_deriv ?_
  simp only [id]
  field_simp
  ring

/-- Decay of the integrand `Ai/x³` for `x ≤ -1`. -/
lemma abs_airy_div_cube_le {x : ℝ} (hx : x ≤ -1) :
    |airyAi x / x ^ 3| ≤ 3 * (-x) ^ (-(13 / 4) : ℝ) := by
  have hx0 : 0 < -x := by linarith
  have hA := abs_airyAi_le_of_nonpos (x := x) (by linarith)
  have habs : |x| = -x := abs_of_neg (by linarith)
  rw [habs] at hA
  have h1 : (1 + -x) ^ (-(1 / 4) : ℝ) ≤ (-x) ^ (-(1 / 4) : ℝ) :=
    Real.rpow_le_rpow_of_nonpos hx0 (by linarith) (by norm_num)
  have e : (-x) ^ (-(13 / 4) : ℝ) = (-x) ^ (-(1 / 4) : ℝ) / (-x) ^ 3 := by
    rw [show (-(13 / 4) : ℝ) = -(1 / 4) + (-3 : ℤ) by norm_num, Real.rpow_add hx0, Real.rpow_intCast]
    rw [zpow_neg, zpow_ofNat]; ring
  rw [abs_div, abs_pow, habs, e]
  have h3 : 0 < (-x) ^ 3 := pow_pos hx0 3
  calc |airyAi x| / (-x) ^ 3 ≤ 3 * (1 + -x) ^ (-(1 / 4) : ℝ) / (-x) ^ 3 := by gcongr
    _ ≤ 3 * (-x) ^ (-(1 / 4) : ℝ) / (-x) ^ 3 := by gcongr
    _ = _ := by ring

/-- `∫_{-S}^t 3 (-x)^{-13/4} ≤ (4/3)(-t)^{-9/4}`. -/
lemma integral_tail_le {S t : ℝ} (hS : -S ≤ t) (ht : t ≤ -1) :
    ∫ x in (-S)..t, 3 * (-x) ^ (-(13 / 4) : ℝ) ≤ 4 / 3 * (-t) ^ (-(9 / 4) : ℝ) := by
  have hd : ∀ x ∈ uIcc (-S) t, HasDerivAt (fun x : ℝ => 4 / 3 * (-x) ^ (-(9 / 4) : ℝ))
      (3 * (-x) ^ (-(13 / 4) : ℝ)) x := by
    intro x hx
    rw [uIcc_of_le hS] at hx
    have hx0 : 0 < -x := by linarith [hx.2]
    have h1 := (Real.hasDerivAt_rpow_const (p := (-(9 / 4) : ℝ)) (x := -x) (Or.inl hx0.ne')).comp x (hasDerivAt_neg x)
    have := h1.const_mul (4 / 3 : ℝ)
    refine this.congr_deriv ?_
    norm_num
    ring
  have hint : IntervalIntegrable (fun x : ℝ => 3 * (-x) ^ (-(13 / 4) : ℝ)) volume (-S) t := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hS]
    intro x hx
    have hx0 : 0 < -x := by linarith [hx.2]
    have h1 := (Real.hasDerivAt_rpow_const (p := (-(13 / 4) : ℝ)) (x := -x) (Or.inl hx0.ne')).comp x (hasDerivAt_neg x)
    exact (h1.continuousAt.const_mul 3).continuousWithinAt
  rw [integral_eq_sub_of_hasDerivAt hd hint]
  have hS0 : 0 < S := by linarith
  have : 0 ≤ 4 / 3 * (-(-S)) ^ (-(9 / 4) : ℝ) := by
    have : 0 < -(-S) := by linarith
    positivity
  simp only [neg_neg] at this ⊢
  linarith only [this]

/-- `B(t) = ∫_{-∞}^t Ai` (improper) for `t ≤ 0`, in the closed form `2/3 - ∫_t^0 Ai`. -/
noncomputable def Bneg (t : ℝ) : ℝ := 2 / 3 - ∫ x in t..0, airyAi x

lemma tendsto_int_bot {t : ℝ} :
    Tendsto (fun S : ℝ => ∫ x in (-S)..t, airyAi x) atTop (𝓝 (Bneg t)) := by
  have h := tendsto_integral_airyAi_bot_zero.sub_const (∫ x in t..0, airyAi x)
  refine h.congr (fun S => ?_)
  have hi : ∀ a b : ℝ, IntervalIntegrable airyAi volume a b :=
    fun a b => differentiable_airyAi.continuous.intervalIntegrable _ _
  have := intervalIntegral.integral_interval_sub_left (hi (-S) 0) (hi (-S) t)
  linarith only [this]

lemma Fk_neg_bound {S : ℝ} (hS : 1 ≤ S) :
    |Fk (-S)| ≤ 10 * S ^ (-(3 / 4) : ℝ) + 3 * S ^ (-2 : ℝ) := by
  have hS0 : 0 < S := by linarith
  have hA := abs_airyAi_le_of_nonpos (x := -S) (by linarith)
  have hB := abs_airyAi'_le_of_nonpos (x := -S) (by linarith)
  rw [abs_neg, abs_of_pos hS0] at hA hB
  have h1 : (1 + S) ^ (1 / 4 : ℝ) ≤ 2 * S ^ (1 / 4 : ℝ) := by
    calc (1 + S) ^ (1 / 4 : ℝ) ≤ (2 * S) ^ (1 / 4 : ℝ) :=
          Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
      _ = 2 ^ (1 / 4 : ℝ) * S ^ (1 / 4 : ℝ) := Real.mul_rpow (by norm_num) hS0.le
      _ ≤ 2 * S ^ (1 / 4 : ℝ) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          calc (2 : ℝ) ^ (1 / 4 : ℝ) ≤ 2 ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 2 := Real.rpow_one 2
  have h2 : (1 + S) ^ (-(1 / 4) : ℝ) ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
  have e1 : S ^ (1 / 4 : ℝ) / S = S ^ (-(3 / 4) : ℝ) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hS0]; norm_num
  have e2 : 1 / S ^ 2 = S ^ (-2 : ℝ) := by
    rw [Real.rpow_neg hS0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, one_div]
  unfold Fk
  have e3 : airyAi' (-S) / (-S) + airyAi (-S) / (-S) ^ 2 = -(airyAi' (-S) / S) + airyAi (-S) / S ^ 2 := by
    ring
  rw [e3]
  refine (abs_add_le _ _).trans ?_
  rw [abs_neg, abs_div, abs_div, abs_of_pos hS0, abs_pow, abs_of_pos hS0]
  have hB' : |airyAi' (-S)| / S ≤ 10 * S ^ (-(3 / 4) : ℝ) := by
    rw [div_le_iff₀ hS0]
    calc |airyAi' (-S)| ≤ 5 * (1 + S) ^ (1 / 4 : ℝ) := hB
      _ ≤ 5 * (2 * S ^ (1 / 4 : ℝ)) := by gcongr
      _ = 10 * (S ^ (1 / 4 : ℝ) / S) * S := by field_simp; norm_num
      _ = 10 * S ^ (-(3 / 4) : ℝ) * S := by rw [e1]
  have hA' : |airyAi (-S)| / S ^ 2 ≤ 3 * S ^ (-2 : ℝ) := by
    rw [div_le_iff₀ (pow_pos hS0 2)]
    calc |airyAi (-S)| ≤ 3 * (1 + S) ^ (-(1 / 4) : ℝ) := hA
      _ ≤ 3 * 1 := by gcongr
      _ = 3 * (1 / S ^ 2) * S ^ 2 := by field_simp
      _ = 3 * S ^ (-2 : ℝ) * S ^ 2 := by rw [e2]
  linarith only [hA', hB']

/-- `|B(t) - F(t)| ≤ (8/3) (-t)^{-9/4}` for `t ≤ -1`. -/
lemma Bneg_sub_Fk_le {t : ℝ} (ht : t ≤ -1) :
    |Bneg t - Fk t| ≤ 8 / 3 * (-t) ^ (-(9 / 4) : ℝ) := by
  have hlim := tendsto_int_bot (t := t)
  have hev : ∀ᶠ S : ℝ in atTop, |(∫ x in (-S)..t, airyAi x) - Fk t| ≤
      (10 * S ^ (-(3 / 4) : ℝ) + 3 * S ^ (-2 : ℝ)) + 8 / 3 * (-t) ^ (-(9 / 4) : ℝ) := by
    filter_upwards [eventually_ge_atTop (-t), eventually_ge_atTop 1] with S hSt hS1
    have hS0 : 0 < S := by linarith
    have hSt' : -S ≤ t := by linarith
    have hi : ∀ a b : ℝ, IntervalIntegrable airyAi volume a b :=
      fun a b => differentiable_airyAi.continuous.intervalIntegrable _ _
    have hj : IntervalIntegrable (fun x : ℝ => airyAi x / x ^ 3) volume (-S) t := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hSt']
      intro x hx
      have hx0 : x ≠ 0 := by linarith [hx.2]
      exact (differentiable_airyAi.continuous.continuousAt.div (continuous_pow 3).continuousAt (pow_ne_zero 3 hx0)).continuousWithinAt
    have hd : ∀ x ∈ uIcc (-S) t, HasDerivAt Fk (airyAi x - 2 * (airyAi x / x ^ 3)) x := by
      intro x hx
      rw [uIcc_of_le hSt'] at hx
      have hx0 : x ≠ 0 := by linarith [hx.2]
      refine (hasDerivAt_Fk hx0).congr_deriv ?_
      ring
    have hftc := integral_eq_sub_of_hasDerivAt hd ((hi (-S) t).sub (hj.const_mul 2))
    rw [integral_sub (hi (-S) t) (hj.const_mul 2), intervalIntegral.integral_const_mul] at hftc
    have hbd : |∫ x in (-S)..t, airyAi x / x ^ 3| ≤ 4 / 3 * (-t) ^ (-(9 / 4) : ℝ) := by
      have h1 := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (a := -S) (b := t)
        (f := fun x : ℝ => airyAi x / x ^ 3) (g := fun x : ℝ => 3 * (-x) ^ (-(13 / 4) : ℝ)) hSt'
        (Filter.Eventually.of_forall (fun x hx => by
          rw [Real.norm_eq_abs]; exact abs_airy_div_cube_le (by linarith [hx.2])))
        (by
          apply ContinuousOn.intervalIntegrable
          rw [uIcc_of_le hSt']
          intro x hx
          have hx0 : 0 < -x := by linarith [hx.2]
          have h1 := (Real.hasDerivAt_rpow_const (p := (-(13 / 4) : ℝ)) (x := -x) (Or.inl hx0.ne')).comp x (hasDerivAt_neg x)
          exact (h1.continuousAt.const_mul 3).continuousWithinAt)
      rw [Real.norm_eq_abs] at h1
      exact h1.trans (integral_tail_le hSt' ht)
    have hF := Fk_neg_bound hS1
    have e : (∫ x in (-S)..t, airyAi x) - Fk t = -Fk (-S) + 2 * ∫ x in (-S)..t, airyAi x / x ^ 3 := by
      linarith only [hftc]
    rw [e]
    calc |-Fk (-S) + 2 * ∫ x in (-S)..t, airyAi x / x ^ 3|
        ≤ |-Fk (-S)| + |2 * ∫ x in (-S)..t, airyAi x / x ^ 3| := abs_add_le _ _
      _ ≤ (10 * S ^ (-(3 / 4) : ℝ) + 3 * S ^ (-2 : ℝ)) + 2 * (4 / 3 * (-t) ^ (-(9 / 4) : ℝ)) := by
          rw [abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
          have := mul_le_mul_of_nonneg_left hbd (by norm_num : (0 : ℝ) ≤ 2)
          linarith only [hF, this]
      _ = _ := by ring
  have hl1 : Tendsto (fun S : ℝ => |(∫ x in (-S)..t, airyAi x) - Fk t|) atTop (𝓝 (|Bneg t - Fk t|)) :=
    (hlim.sub_const _).abs
  have hl2 : Tendsto (fun S : ℝ => (10 * S ^ (-(3 / 4) : ℝ) + 3 * S ^ (-2 : ℝ)) +
      8 / 3 * (-t) ^ (-(9 / 4) : ℝ)) atTop (𝓝 ((10 * 0 + 3 * 0) + 8 / 3 * (-t) ^ (-(9 / 4) : ℝ))) := by
    refine Tendsto.add_const _ (Tendsto.add ?_ ?_)
    · exact (tendsto_rpow_neg_atTop (by norm_num)).const_mul 10
    · exact (tendsto_rpow_neg_atTop (by norm_num)).const_mul 3
  have := le_of_tendsto_of_tendsto hl1 hl2 hev
  simpa using this

/-- **Decay of the Airy primitives on the negative axis** (`cts:tip-shared` (c)): for `t ≤ -1`,
`|B(t)| ≤ 16 |t|^{-3/4}` and `|t B(t) - Ai'(t)| ≤ 16 |t|^{-5/4}`, `B = ∫_{-∞}^t Ai`. -/
theorem Bneg_decay {t : ℝ} (ht : t ≤ -1) :
    |Bneg t| ≤ 16 * (-t) ^ (-(3 / 4) : ℝ) ∧ |t * Bneg t - airyAi' t| ≤ 16 * (-t) ^ (-(5 / 4) : ℝ) := by
  set r : ℝ := -t with hr
  have hr1 : 1 ≤ r := by rw [hr]; linarith
  have hr0 : 0 < r := by linarith
  have ht' : t = -r := by rw [hr]; ring
  have hmain := Bneg_sub_Fk_le ht
  rw [← hr] at hmain
  have hA := abs_airyAi_le_of_nonpos (x := t) (by linarith)
  have hB := abs_airyAi'_le_of_nonpos (x := t) (by linarith)
  have habs : |t| = r := by rw [ht', abs_neg, abs_of_pos hr0]
  rw [habs] at hA hB
  have h1 : (1 + r) ^ (1 / 4 : ℝ) ≤ 2 * r ^ (1 / 4 : ℝ) := by
    calc (1 + r) ^ (1 / 4 : ℝ) ≤ (2 * r) ^ (1 / 4 : ℝ) :=
          Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
      _ = 2 ^ (1 / 4 : ℝ) * r ^ (1 / 4 : ℝ) := Real.mul_rpow (by norm_num) hr0.le
      _ ≤ 2 * r ^ (1 / 4 : ℝ) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          calc (2 : ℝ) ^ (1 / 4 : ℝ) ≤ 2 ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 2 := Real.rpow_one 2
  have h2 : (1 + r) ^ (-(1 / 4) : ℝ) ≤ r ^ (-(1 / 4) : ℝ) :=
    Real.rpow_le_rpow_of_nonpos hr0 (by linarith) (by norm_num)
  have e1 : r ^ (1 / 4 : ℝ) / r = r ^ (-(3 / 4) : ℝ) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hr0]; norm_num
  have e2 : r ^ (-(1 / 4) : ℝ) / r = r ^ (-(5 / 4) : ℝ) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hr0]; norm_num
  have e3 : r ^ (-(1 / 4) : ℝ) / r ^ 2 = r ^ (-(9 / 4) : ℝ) := by
    have h2' : r ^ 2 = r ^ (2 : ℝ) := by rw [← Real.rpow_natCast]; norm_num
    rw [h2', div_eq_mul_inv, ← Real.rpow_neg hr0.le, ← Real.rpow_add hr0]; norm_num
  have e4 : r * r ^ (-(9 / 4) : ℝ) = r ^ (-(5 / 4) : ℝ) := by
    calc r * r ^ (-(9 / 4) : ℝ) = r ^ (1 : ℝ) * r ^ (-(9 / 4) : ℝ) := by rw [Real.rpow_one]
      _ = r ^ (1 + -(9 / 4) : ℝ) := (Real.rpow_add hr0 _ _).symm
      _ = _ := by norm_num
  have m1 : r ^ (-(9 / 4) : ℝ) ≤ r ^ (-(3 / 4) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hr1 (by norm_num)
  have m2 : r ^ (-(5 / 4) : ℝ) ≥ 0 := by positivity
  have hp1 : |airyAi' t / t| ≤ 10 * r ^ (-(3 / 4) : ℝ) := by
    rw [abs_div, habs, div_le_iff₀ hr0]
    calc |airyAi' t| ≤ 5 * (1 + r) ^ (1 / 4 : ℝ) := hB
      _ ≤ 5 * (2 * r ^ (1 / 4 : ℝ)) := by gcongr
      _ = 10 * (r ^ (1 / 4 : ℝ) / r) * r := by field_simp; norm_num
      _ = 10 * r ^ (-(3 / 4) : ℝ) * r := by rw [e1]
  have hp2 : |airyAi t / t ^ 2| ≤ 3 * r ^ (-(9 / 4) : ℝ) := by
    rw [abs_div, abs_pow, habs, div_le_iff₀ (pow_pos hr0 2)]
    calc |airyAi t| ≤ 3 * (1 + r) ^ (-(1 / 4) : ℝ) := hA
      _ ≤ 3 * r ^ (-(1 / 4) : ℝ) := by gcongr
      _ = 3 * (r ^ (-(1 / 4) : ℝ) / r ^ 2) * r ^ 2 := by field_simp
      _ = 3 * r ^ (-(9 / 4) : ℝ) * r ^ 2 := by rw [e3]
  have hp3 : |airyAi t / t| ≤ 3 * r ^ (-(5 / 4) : ℝ) := by
    rw [abs_div, habs, div_le_iff₀ hr0]
    calc |airyAi t| ≤ 3 * (1 + r) ^ (-(1 / 4) : ℝ) := hA
      _ ≤ 3 * r ^ (-(1 / 4) : ℝ) := by gcongr
      _ = 3 * (r ^ (-(1 / 4) : ℝ) / r) * r := by field_simp
      _ = 3 * r ^ (-(5 / 4) : ℝ) * r := by rw [e2]
  constructor
  · have hF : |Fk t| ≤ 10 * r ^ (-(3 / 4) : ℝ) + 3 * r ^ (-(9 / 4) : ℝ) := by
      unfold Fk
      refine (abs_add_le _ _).trans ?_
      linarith only [hp1, hp2]
    have : |Bneg t| ≤ |Fk t| + |Bneg t - Fk t| := by
      calc |Bneg t| = |Fk t + (Bneg t - Fk t)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    have hx0 : 0 ≤ r ^ (-(3 / 4) : ℝ) := by positivity
    linarith only [this, hF, hmain, m1, hx0]
  · have e : t * Bneg t - airyAi' t = t * (Bneg t - Fk t) + airyAi t / t := by
      unfold Fk
      have ht0 : t ≠ 0 := by linarith
      field_simp
      ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, habs]
    have : r * |Bneg t - Fk t| ≤ r * (8 / 3 * r ^ (-(9 / 4) : ℝ)) :=
      mul_le_mul_of_nonneg_left hmain hr0.le
    have e5 : r * (8 / 3 * r ^ (-(9 / 4) : ℝ)) = 8 / 3 * (r * r ^ (-(9 / 4) : ℝ)) := by ring
    rw [e5, e4] at this
    linarith only [this, hp3, m2]

/-- info: 'FormalResearch.Special.AiryPrimNeg.Bneg_decay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Bneg_decay

end FormalResearch.Special.AiryPrimNeg
