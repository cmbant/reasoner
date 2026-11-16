module

public import FormalResearch.Special.AiryZeroSecondOrder

/-!
# Limit and spacing corollaries of the second-order zero asymptotics

Short consequences of `airyZero_second_order` (`AiryZeroSecondOrder`, DLMF 9.9.18 to relative order `t^{-4}`),
with `t_n = (3π/2)(n - 1/4)` and `T₂(t) = t^{2/3}(1 + 5/(48 t²))`:

* `airyZero_nat_div_shift`, `airyZero_nat_div_T_tendsto`: `n / t_n → 2/(3π)`;
* **`airyZero_delta_tendsto`**: `n^{4/3} (a_n + t_n^{2/3}) → -(5/48) (3π/2)^{-4/3}` (the sharp limit, `= -0.013185…`);
* `airyZero_abs_div_tendsto`: `|a_n| / n^{2/3} → (3π/2)^{2/3}`;
* **`airyZero_gap_second`**: for `n ≥ 2`, `|(a_n - a_{n+1}) - (T₂(t_{n+1}) - T₂(t_n))| ≤ 4 t_n^{-10/3}` (the second-order
  spacing: error `O(n^{-10/3})` against the gap `≍ n^{-1/3}`);
* **`airyZero_gap_tendsto`**: `n^{1/3} (a_n - a_{n+1}) → (2/3)(3π/2)^{2/3}` (`= 1.8739…`, the limit quoted in `AiryZeroSpacing`).

Proved here: everything stated; no numerics enter the proofs.  The limit constants were checked against mpmath (30 digits) in
`AiryZeroSecondOrder` (`n^{4/3} δ_n = -0.01786, -0.01547, … → -0.013185`).  **Not formalised:** rates of convergence of the
limits (they follow from the explicit second-order bound with `O(1/n)` corrections but are not written).
-/

@[expose] public section

open Set Filter Topology
open scoped Real

namespace FormalResearch.Special

/-- `n / ((3π/2)(n + c)) → 2/(3π)` for every shift `c`. -/
theorem airyZero_nat_div_shift (c : ℝ) :
    Tendsto (fun n : ℕ => (n : ℝ) / (3 * π / 2 * ((n : ℝ) + c))) atTop (𝓝 (2 / (3 * π))) := by
  have h0 : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
  have h1 : Tendsto (fun n : ℕ => 1 + c * (1 / (n : ℝ))) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).add (h0.const_mul c)
  have h2 : Tendsto (fun n : ℕ => 2 / (3 * π) / (1 + c * (1 / (n : ℝ)))) atTop (𝓝 (2 / (3 * π) / 1)) :=
    tendsto_const_nhds.div h1 one_ne_zero
  rw [div_one] at h2
  refine h2.congr' ?_
  filter_upwards [tendsto_natCast_atTop_atTop.eventually_gt_atTop (|c|)] with n hn
  have hn0 : (0 : ℝ) < n := lt_of_le_of_lt (abs_nonneg c) hn
  have hnc : (n : ℝ) + c ≠ 0 := by
    have := neg_abs_le c
    intro h; linarith
  have hpi := Real.pi_pos
  field_simp

/-- `n / t_n → 2/(3π)`. -/
theorem airyZero_nat_div_T_tendsto :
    Tendsto (fun n : ℕ => (n : ℝ) / airyZeroT n) atTop (𝓝 (2 / (3 * π))) := by
  refine (airyZero_nat_div_shift (-1 / 4)).congr fun n => ?_
  unfold airyZeroT; ring_nf

lemma airyZero_nat_rpow_div (n : ℕ) (hn : 1 ≤ n) (c : ℝ) :
    (n : ℝ) ^ c * airyZeroT n ^ (-c) = ((n : ℝ) / airyZeroT n) ^ c := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.div_rpow hn0.le (airyZeroT_pos hn).le, Real.rpow_neg (airyZeroT_pos hn).le, div_eq_mul_inv]

/-- **The sharp limit of the deviation**: `n^{4/3} (a_n + t_n^{2/3}) → -(5/48) (3π/2)^{-4/3}`. -/
theorem airyZero_delta_tendsto :
    Tendsto (fun n : ℕ => (n : ℝ) ^ (4 / 3 : ℝ) * (airyZero n + airyZeroT n ^ (2 / 3 : ℝ))) atTop
      (𝓝 (-(5 / 48) * (3 * π / 2) ^ (-(4 / 3) : ℝ))) := by
  have hX : Tendsto (fun n : ℕ => -(5 / 48) * ((n : ℝ) / airyZeroT n) ^ (4 / 3 : ℝ)) atTop
      (𝓝 (-(5 / 48) * (2 / (3 * π)) ^ (4 / 3 : ℝ))) :=
    (airyZero_nat_div_T_tendsto.rpow_const (Or.inr (by norm_num))).const_mul _
  have hlim : (2 / (3 * π)) ^ (4 / 3 : ℝ) = (3 * π / 2) ^ (-(4 / 3) : ℝ) := by
    rw [Real.rpow_neg (by positivity), ← Real.inv_rpow (by positivity)]
    congr 1; field_simp
  rw [hlim] at hX
  have hY : Tendsto (fun n : ℕ => (n : ℝ) ^ (4 / 3 : ℝ) *
      (airyZero n + airyZeroT n ^ (2 / 3 : ℝ) + 5 / 48 * airyZeroT n ^ (-(4 / 3) : ℝ))) atTop (𝓝 0) := by
    have hsq : Tendsto (fun n : ℕ => 2 * ((n : ℝ) ^ 2)⁻¹) atTop (𝓝 0) := by
      have := (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (α := ℝ) (n := 2) two_ne_zero
        |>.comp tendsto_natCast_atTop_atTop)).const_mul 2
      simpa using this
    refine squeeze_zero_norm' ?_ hsq
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have h := airyZero_delta_second hn
    have ht0 := airyZeroT_pos (by omega : 1 ≤ n)
    have hge : (n : ℝ) ≤ airyZeroT n := airyZeroT_ge (by omega)
    have hpow : airyZeroT n ^ (-(10 / 3) : ℝ) ≤ (n : ℝ) ^ (-(10 / 3) : ℝ) :=
      Real.rpow_le_rpow_of_nonpos hn0 hge (by norm_num)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hn0 _)]
    calc (n : ℝ) ^ (4 / 3 : ℝ) * |_| ≤ (n : ℝ) ^ (4 / 3 : ℝ) * (2 * (n : ℝ) ^ (-(10 / 3) : ℝ)) := by
          gcongr; exact h.trans (by linarith)
      _ = 2 * ((n : ℝ) ^ 2)⁻¹ := by
          rw [← mul_assoc, mul_comm _ (2 : ℝ), mul_assoc, ← Real.rpow_add hn0]
          have : (4 / 3 : ℝ) + -(10 / 3) = -(2 : ℝ) := by norm_num
          rw [this, Real.rpow_neg hn0.le]; norm_cast
  have := hX.add hY
  rw [add_zero] at this
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have := airyZero_nat_rpow_div n hn (4 / 3)
  rw [mul_add, mul_add, ← this]
  ring

/-- **`|a_n| / n^{2/3} → (3π/2)^{2/3}`** (the Weyl law for the zeros of `Ai`). -/
theorem airyZero_abs_div_tendsto :
    Tendsto (fun n : ℕ => (-airyZero n) / (n : ℝ) ^ (2 / 3 : ℝ)) atTop (𝓝 ((3 * π / 2) ^ (2 / 3 : ℝ))) := by
  have h1 : Tendsto (fun n : ℕ => ((n : ℝ) / airyZeroT n) ^ (-(2 / 3) : ℝ)) atTop
      (𝓝 ((2 / (3 * π)) ^ (-(2 / 3) : ℝ))) :=
    airyZero_nat_div_T_tendsto.rpow_const (Or.inl (by positivity))
  have hlim : (2 / (3 * π)) ^ (-(2 / 3) : ℝ) = (3 * π / 2) ^ (2 / 3 : ℝ) := by
    rw [Real.rpow_neg (by positivity), ← Real.inv_rpow (by positivity)]
    congr 1; field_simp
  rw [hlim] at h1
  have hn : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(2 : ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have h2 := (hn.mul airyZero_delta_tendsto).congr' (Eventually.of_forall fun _ => rfl)
  rw [zero_mul] at h2
  have h3 := h1.sub h2
  rw [sub_zero] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have ht0 := airyZeroT_pos hn1
  have e1 : ((n : ℝ) / airyZeroT n) ^ (-(2 / 3) : ℝ) = airyZeroT n ^ (2 / 3 : ℝ) / (n : ℝ) ^ (2 / 3 : ℝ) := by
    rw [← inv_div, Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity), neg_neg,
      Real.div_rpow ht0.le hn0.le]
  have e2 : (n : ℝ) ^ (-(2 : ℝ)) * (n : ℝ) ^ (4 / 3 : ℝ) = ((n : ℝ) ^ (2 / 3 : ℝ))⁻¹ := by
    rw [← Real.rpow_add hn0, ← Real.rpow_neg hn0.le]; norm_num
  have hp : 0 < (n : ℝ) ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hn0 _
  rw [e1, ← mul_assoc, e2]
  field_simp
  ring
/-- `T₂(t) = t^{2/3} (1 + 5/(48 t²)) = t^{2/3} + (5/48) t^{-4/3}`. -/
lemma airyT2_eq {t : ℝ} (ht : 0 < t) :
    t ^ (2 / 3 : ℝ) * (1 + 5 / (48 * t ^ 2)) = t ^ (2 / 3 : ℝ) + 5 / 48 * t ^ (-(4 / 3) : ℝ) := by
  obtain ⟨hw3, hw2, hw4, -⟩ := airySO_rpow ht
  have ht2 : t ^ 2 = (t ^ (1 / 3 : ℝ)) ^ 6 := by
    calc t ^ 2 = ((t ^ (1 / 3 : ℝ)) ^ 3) ^ 2 := by rw [hw3]
      _ = _ := by ring
  have hg0 : 0 < t ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos ht _
  rw [hw2, hw4, ht2]; field_simp

/-- **Second-order spacing of the zeros** (`n ≥ 2`): with `T₂(t) = t^{2/3}(1 + 5/(48 t²))`,
`|(a_n - a_{n+1}) - (T₂(t_{n+1}) - T₂(t_n))| ≤ 4 t_n^{-10/3}`. -/
theorem airyZero_gap_second {n : ℕ} (hn : 2 ≤ n) :
    |(airyZero n - airyZero (n + 1)) -
        (airyZeroT (n + 1) ^ (2 / 3 : ℝ) * (1 + 5 / (48 * airyZeroT (n + 1) ^ 2)) -
          airyZeroT n ^ (2 / 3 : ℝ) * (1 + 5 / (48 * airyZeroT n ^ 2)))| ≤ 4 * airyZeroT n ^ (-(10 / 3) : ℝ) := by
  have h1 := airyZero_second_order hn
  have h2 := airyZero_second_order (by omega : 2 ≤ n + 1)
  have ht0 := airyZeroT_pos (by omega : 1 ≤ n)
  have hle : airyZeroT n ≤ airyZeroT (n + 1) := by unfold airyZeroT; push_cast; nlinarith [Real.pi_pos]
  have hp : airyZeroT (n + 1) ^ (-(10 / 3) : ℝ) ≤ airyZeroT n ^ (-(10 / 3) : ℝ) :=
    Real.rpow_le_rpow_of_nonpos ht0 hle (by norm_num)
  have e : (airyZero n - airyZero (n + 1)) -
        (airyZeroT (n + 1) ^ (2 / 3 : ℝ) * (1 + 5 / (48 * airyZeroT (n + 1) ^ 2)) -
          airyZeroT n ^ (2 / 3 : ℝ) * (1 + 5 / (48 * airyZeroT n ^ 2))) =
      (airyZero n + airyZeroT n ^ (2 / 3 : ℝ) * (1 + 5 / (48 * airyZeroT n ^ 2))) -
        (airyZero (n + 1) + airyZeroT (n + 1) ^ (2 / 3 : ℝ) * (1 + 5 / (48 * airyZeroT (n + 1) ^ 2))) := by ring
  rw [e]
  refine (abs_sub _ _).trans ?_
  linarith

/-- Mean value bounds for `x ↦ x^{2/3}`: for `0 < a < b`,
`(2/3)(b - a) b^{-1/3} ≤ b^{2/3} - a^{2/3} ≤ (2/3)(b - a) a^{-1/3}`. -/
lemma airyRpow23_sub {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    2 / 3 * (b - a) * b ^ (-(1 / 3) : ℝ) ≤ b ^ (2 / 3 : ℝ) - a ^ (2 / 3 : ℝ) ∧
      b ^ (2 / 3 : ℝ) - a ^ (2 / 3 : ℝ) ≤ 2 / 3 * (b - a) * a ^ (-(1 / 3) : ℝ) := by
  have hd : ∀ x ∈ Ioo a b, HasDerivAt (fun x : ℝ => x ^ (2 / 3 : ℝ)) (2 / 3 * x ^ (2 / 3 - 1 : ℝ)) x := by
    intro x hx
    exact Real.hasDerivAt_rpow_const (Or.inl (ha.trans hx.1).ne')
  have hc : ContinuousOn (fun x : ℝ => x ^ (2 / 3 : ℝ)) (Icc a b) :=
    fun x hx => (Real.continuousAt_rpow_const x _ (Or.inl (ha.trans_le hx.1).ne')).continuousWithinAt
  obtain ⟨ξ, hξ, hξe⟩ := exists_hasDerivAt_eq_slope (fun x : ℝ => x ^ (2 / 3 : ℝ)) _ hab hc hd
  have hba : 0 < b - a := by linarith
  have hdiff : b ^ (2 / 3 : ℝ) - a ^ (2 / 3 : ℝ) = 2 / 3 * ξ ^ (-(1 / 3) : ℝ) * (b - a) := by
    rw [eq_div_iff hba.ne'] at hξe
    rw [← hξe]; norm_num
  have h1 : b ^ (-(1 / 3) : ℝ) ≤ ξ ^ (-(1 / 3) : ℝ) :=
    Real.rpow_le_rpow_of_nonpos (ha.trans hξ.1) hξ.2.le (by norm_num)
  have h2 : ξ ^ (-(1 / 3) : ℝ) ≤ a ^ (-(1 / 3) : ℝ) :=
    Real.rpow_le_rpow_of_nonpos ha hξ.1.le (by norm_num)
  rw [hdiff]
  constructor <;> nlinarith

/-- **`n^{1/3}(a_n - a_{n+1}) → (2/3)(3π/2)^{2/3}`** (`= 1.8739…`): the limit gap, from the second-order bound. -/
theorem airyZero_gap_tendsto :
    Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 3 : ℝ) * (airyZero n - airyZero (n + 1))) atTop
      (𝓝 (2 / 3 * (3 * π / 2) ^ (2 / 3 : ℝ))) := by
  have hL : Tendsto (fun n : ℕ => (n : ℝ) / airyZeroT n) atTop (𝓝 (2 / (3 * π))) := airyZero_nat_div_T_tendsto
  have hL' : Tendsto (fun n : ℕ => (n : ℝ) / airyZeroT (n + 1)) atTop (𝓝 (2 / (3 * π))) := by
    refine (airyZero_nat_div_shift (3 / 4)).congr fun n => ?_
    unfold airyZeroT; push_cast; ring_nf
  have hc : 2 / 3 * (3 * π / 2) ^ (2 / 3 : ℝ) = 2 / 3 * (3 * π / 2) * (2 / (3 * π)) ^ (1 / 3 : ℝ) := by
    have hpi := Real.pi_pos
    have h32 : (0 : ℝ) < 3 * π / 2 := by positivity
    have : (3 * π / 2) ^ (2 / 3 : ℝ) = (3 * π / 2) * (2 / (3 * π)) ^ (1 / 3 : ℝ) := by
      have e : (2 / (3 * π)) = (3 * π / 2) ^ (-1 : ℝ) := by rw [Real.rpow_neg_one]; field_simp
      rw [e, ← Real.rpow_mul h32.le]
      conv_lhs => rw [show (2 / 3 : ℝ) = 1 + -1 / 3 by norm_num, Real.rpow_add h32, Real.rpow_one]
      norm_num
    rw [this]; ring
  -- the squeezed main term
  have hlo : Tendsto (fun n : ℕ => 2 / 3 * (3 * π / 2) * ((n : ℝ) / airyZeroT (n + 1)) ^ (1 / 3 : ℝ)) atTop
      (𝓝 (2 / 3 * (3 * π / 2) * (2 / (3 * π)) ^ (1 / 3 : ℝ))) :=
    (hL'.rpow_const (Or.inr (by norm_num))).const_mul _
  have hhi : Tendsto (fun n : ℕ => 2 / 3 * (3 * π / 2) * ((n : ℝ) / airyZeroT n) ^ (1 / 3 : ℝ)) atTop
      (𝓝 (2 / 3 * (3 * π / 2) * (2 / (3 * π)) ^ (1 / 3 : ℝ))) :=
    (hL.rpow_const (Or.inr (by norm_num))).const_mul _
  have hD : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 3 : ℝ) *
      (airyZeroT (n + 1) ^ (2 / 3 : ℝ) - airyZeroT n ^ (2 / 3 : ℝ))) atTop
      (𝓝 (2 / 3 * (3 * π / 2) * (2 / (3 * π)) ^ (1 / 3 : ℝ))) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      have ht0 := airyZeroT_pos hn
      have hlt : airyZeroT n < airyZeroT (n + 1) := by unfold airyZeroT; push_cast; nlinarith [Real.pi_pos]
      have hB := airyZeroT_pos (by omega : 1 ≤ n + 1)
      have := (airyRpow23_sub ht0 hlt).1
      have hh : airyZeroT (n + 1) - airyZeroT n = 3 * π / 2 := by unfold airyZeroT; push_cast; ring
      rw [hh] at this
      have e : ((n : ℝ) / airyZeroT (n + 1)) ^ (1 / 3 : ℝ) =
          (n : ℝ) ^ (1 / 3 : ℝ) * airyZeroT (n + 1) ^ (-(1 / 3) : ℝ) := by
        rw [Real.div_rpow hn0.le hB.le, Real.rpow_neg hB.le, div_eq_mul_inv]
      rw [e]
      have := mul_le_mul_of_nonneg_left this (Real.rpow_pos_of_pos hn0 (1 / 3)).le
      nlinarith
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      have ht0 := airyZeroT_pos hn
      have hlt : airyZeroT n < airyZeroT (n + 1) := by unfold airyZeroT; push_cast; nlinarith [Real.pi_pos]
      have := (airyRpow23_sub ht0 hlt).2
      have hh : airyZeroT (n + 1) - airyZeroT n = 3 * π / 2 := by unfold airyZeroT; push_cast; ring
      rw [hh] at this
      have e : ((n : ℝ) / airyZeroT n) ^ (1 / 3 : ℝ) =
          (n : ℝ) ^ (1 / 3 : ℝ) * airyZeroT n ^ (-(1 / 3) : ℝ) := by
        rw [Real.div_rpow hn0.le ht0.le, Real.rpow_neg ht0.le, div_eq_mul_inv]
      rw [e]
      have := mul_le_mul_of_nonneg_left this (Real.rpow_pos_of_pos hn0 (1 / 3)).le
      nlinarith
  -- the remainder
  have hR : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 3 : ℝ) * (airyZero n - airyZero (n + 1)) -
      (n : ℝ) ^ (1 / 3 : ℝ) * (airyZeroT (n + 1) ^ (2 / 3 : ℝ) - airyZeroT n ^ (2 / 3 : ℝ))) atTop (𝓝 0) := by
    have hq : Tendsto (fun n : ℕ => 5 * (1 / (n : ℝ))) atTop (𝓝 0) := by
      simpa using tendsto_one_div_atTop_nhds_zero_nat.const_mul (5 : ℝ)
    refine squeeze_zero_norm' ?_ hq
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    have ht0 := airyZeroT_pos (by omega : 1 ≤ n)
    have hB := airyZeroT_pos (by omega : 1 ≤ n + 1)
    have hge : (n : ℝ) ≤ airyZeroT n := airyZeroT_ge (by omega)
    have hle : airyZeroT n ≤ airyZeroT (n + 1) := by unfold airyZeroT; push_cast; nlinarith [Real.pi_pos]
    have hg := airyZero_gap_second hn
    rw [airyT2_eq ht0, airyT2_eq hB] at hg
    set A := airyZeroT n
    set B := airyZeroT (n + 1)
    have hAB : |B ^ (-(4 / 3) : ℝ) - A ^ (-(4 / 3) : ℝ)| ≤ A ^ (-(4 / 3) : ℝ) := by
      have h1 : B ^ (-(4 / 3) : ℝ) ≤ A ^ (-(4 / 3) : ℝ) := Real.rpow_le_rpow_of_nonpos ht0 hle (by norm_num)
      have h2 : 0 < B ^ (-(4 / 3) : ℝ) := Real.rpow_pos_of_pos hB _
      rw [abs_le]; constructor <;> linarith
    have hm : (n : ℝ) ^ (-(4 / 3) : ℝ) ≥ A ^ (-(4 / 3) : ℝ) :=
      Real.rpow_le_rpow_of_nonpos hn0 hge (by norm_num)
    have hm2 : A ^ (-(10 / 3) : ℝ) ≤ (n : ℝ) ^ (-(10 / 3) : ℝ) := Real.rpow_le_rpow_of_nonpos hn0 hge (by norm_num)
    have e1 : (n : ℝ) ^ (1 / 3 : ℝ) * (n : ℝ) ^ (-(4 / 3) : ℝ) = 1 / n := by
      rw [← Real.rpow_add hn0]; norm_num [Real.rpow_neg_one]
    have e2 : (n : ℝ) ^ (1 / 3 : ℝ) * (n : ℝ) ^ (-(10 / 3) : ℝ) = 1 / (n : ℝ) ^ 3 := by
      rw [← Real.rpow_add hn0]; rw [show (1 / 3 : ℝ) + -(10 / 3) = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg hn0.le,
        Real.rpow_natCast]; simp
    have hn3 : 1 / (n : ℝ) ^ 3 ≤ 1 / n := by
      apply one_div_le_one_div_of_le hn0
      have : (0 : ℝ) ≤ (n : ℝ) ^ 2 - 1 := by nlinarith
      nlinarith [mul_nonneg hn0.le this]
    have hp1 : 0 < (n : ℝ) ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hn0 _
    rw [Real.norm_eq_abs, ← mul_sub, abs_mul, abs_of_pos hp1]
    have key : |(airyZero n - airyZero (n + 1)) - (B ^ (2 / 3 : ℝ) - A ^ (2 / 3 : ℝ))| ≤
        5 / 48 * A ^ (-(4 / 3) : ℝ) + 4 * A ^ (-(10 / 3) : ℝ) := by
      have e : (airyZero n - airyZero (n + 1)) - (B ^ (2 / 3 : ℝ) - A ^ (2 / 3 : ℝ)) =
          ((airyZero n - airyZero (n + 1)) - (B ^ (2 / 3 : ℝ) + 5 / 48 * B ^ (-(4 / 3) : ℝ) -
            (A ^ (2 / 3 : ℝ) + 5 / 48 * A ^ (-(4 / 3) : ℝ)))) +
          5 / 48 * (B ^ (-(4 / 3) : ℝ) - A ^ (-(4 / 3) : ℝ)) := by ring
      rw [e]
      refine (abs_add_le _ _).trans ?_
      have : |5 / 48 * (B ^ (-(4 / 3) : ℝ) - A ^ (-(4 / 3) : ℝ))| ≤ 5 / 48 * A ^ (-(4 / 3) : ℝ) := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 5 / 48)]; gcongr
      linarith
    calc (n : ℝ) ^ (1 / 3 : ℝ) * |_| ≤ (n : ℝ) ^ (1 / 3 : ℝ) *
          (5 / 48 * (n : ℝ) ^ (-(4 / 3) : ℝ) + 4 * (n : ℝ) ^ (-(10 / 3) : ℝ)) := by
          gcongr
          · linarith [key]
      _ = 5 / 48 * (1 / n) + 4 * (1 / (n : ℝ) ^ 3) := by rw [mul_add, ← e1, ← e2]; ring
      _ ≤ 5 * (1 / (n : ℝ)) := by
          have : 0 < 1 / (n : ℝ) := by positivity
          nlinarith
  have := hD.add hR
  rw [hc]
  refine (by simpa using this : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 3 : ℝ) *
      (airyZeroT (n + 1) ^ (2 / 3 : ℝ) - airyZeroT n ^ (2 / 3 : ℝ)) +
      ((n : ℝ) ^ (1 / 3 : ℝ) * (airyZero n - airyZero (n + 1)) -
      (n : ℝ) ^ (1 / 3 : ℝ) * (airyZeroT (n + 1) ^ (2 / 3 : ℝ) - airyZeroT n ^ (2 / 3 : ℝ)))) atTop _).congr fun n => by ring

/-- info: 'FormalResearch.Special.airyZero_nat_div_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyZero_nat_div_shift

/-- info: 'FormalResearch.Special.airyZero_nat_div_T_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyZero_nat_div_T_tendsto

/-- info: 'FormalResearch.Special.airyZero_delta_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyZero_delta_tendsto

/-- info: 'FormalResearch.Special.airyZero_abs_div_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyZero_abs_div_tendsto

/-- info: 'FormalResearch.Special.airyZero_gap_second' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyZero_gap_second

/-- info: 'FormalResearch.Special.airyZero_gap_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyZero_gap_tendsto

end FormalResearch.Special
