module

public import FormalResearch.Special.AiryZeroSecondOrderPhase

/-!
# DLMF 9.9.18: the zeros of `Ai` to relative order `t^{-4}`

With `t_n = (3π/2)(n - 1/4) = 3π(4n - 1)/8` (the argument of DLMF 9.9.18) the `n`-th zero of `Ai` is
`a_n = -T(t_n)`, `T(t) = t^{2/3} (1 + 5/(48 t²) + O(t^{-4}))`.  This module proves the explicit form
`|a_n + t_n^{2/3} (1 + 5/(48 t_n²))| ≤ 2 t_n^{-10/3}` (`t^{2/3 - 4} = t^{-10/3}`) for `n ≥ 2` and the corollaries used by
the CFT survey's "Lemma Z" (UPPER_TRANSFER): `δ_n = a_n + t_n^{2/3}` satisfies
`|δ_n + (5/48) t_n^{-4/3}| ≤ 2 t_n^{-10/3}`, hence `δ_n = -(5/48) t_n^{-4/3} (1 + O(t_n^{-2}))` and `|δ_n| ≤ C n^{-4/3}`.

**Route.**  `airyZero_phase_second` (`AiryZeroSecondOrderPhase`: from the `u₂`-corrected expansion of `Ai(-r²)`,
`AiryZeroSecondOrderChi`, itself from the fourth-order saddle estimate `AiryZeroSecondOrderSaddle`) gives, with
`s = r³ = (-a_n)^{3/2}`, `s - 5/(32 s) = t_n + O(s^{-3})`.  Inverting, `s = t + 5/(32 t) + O(t^{-3})`, and
`s^{2/3} = t^{2/3}(1 + 5/(48 t²)) + O(t^{-10/3})` (`airySO_invert`, via `|a² - b²| min(a, b) ≤ |a³ - b³|`,
`airyMin_lemma`).

* `airySO_invert`: the real inversion lemma;
* **`airyZero_second_order`**: for `n ≥ 2`, `|a_n + t^{2/3}(1 + 5/(48 t²))| ≤ 2 t^{-10/3}` (explicit constant `2`),
  and `≤ 2 n^{-10/3}` (`airyZero_second_order_n`);
* **`airyZero_delta_second`**: `|a_n + t^{2/3} + (5/48) t^{-4/3}| ≤ 2 t^{-10/3}` for `n ≥ 2`;
* **`airyZero_second_order_exists`**: `∃ C, ∀ n ≥ 1, |a_n + t_n^{2/3}(1 + 5/(48 t_n²))| ≤ C t_n^{-10/3}` and
  **`airyZero_delta_exists`**: `∃ C, ∀ n ≥ 1, |a_n + t_n^{2/3}| ≤ C n^{-4/3}` (the case `n = 1` is absorbed into
  the constant; no numerical value of `a_1` is used).

Numerically (mpmath, 30 digits, `1 ≤ n ≤ 3000`): `t_n^{10/3} (a_n + T₂(t_n))` rises from `0.1004` (`n = 1`) to the limit
`5/36 = 0.13889` (the next term `-(5/36) t^{-4}` of DLMF 9.9.18), so the proved constant `2` is about `14` times the
truth; `n^{4/3} δ_n` equals `-0.01786` (`n = 1`), `-0.01547` (`n = 2`) and tends to `-(5/48)(3π/2)^{-4/3} = -0.013185`.

Proved here: everything stated.  The `-(5/36) t^{-4}` coefficient (DLMF 9.9.18's next term, via the `u₃`-term of the saddle
expansion) and the `Tendsto` and spacing corollaries are `AiryZeroThird*`.  **Not formalised:** the derivative/`Ai'`
analogue (DLMF 9.9.19).
-/

@[expose] public section

open Set
open scoped Real

namespace FormalResearch.Special

/-- **Inversion of `s - 5/(32 s) = t + O(s^{-3})`** at the level of `r² = s^{2/3}`, `g² = t^{2/3}`:
with `s = r³`, `t = g³`, `r > 2`, `|s - t - 5/(32 s)| ≤ (33/20)/s³` and `|s - t| ≤ (3/5)/s`, one has
`|r² - g² - 5/(48 g⁴)| ≤ 2/g^{10}`. -/
theorem airySO_invert {r g : ℝ} (hr : 2 < r) (hg : 0 < g)
    (H1 : |r ^ 3 - g ^ 3 - 5 / (32 * r ^ 3)| ≤ 33 / 20 / (r ^ 3) ^ 3)
    (H2 : |r ^ 3 - g ^ 3| ≤ 3 / 5 / r ^ 3) :
    |r ^ 2 - g ^ 2 - 5 / (48 * g ^ 4)| ≤ 2 / g ^ 10 := by
  have hr0 : 0 < r := by linarith
  set s := r ^ 3 with hsdef
  set t := g ^ 3 with htdef
  have hs : 8 < s := by nlinarith [pow_lt_pow_left₀ hr (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : 3 ≠ 0)]
  have hs0 : 0 < s := by linarith
  have ht0 : 0 < t := pow_pos hg 3
  have hH2 : |s - t| ≤ 3 / 40 := by
    refine H2.trans ?_
    rw [div_le_div_iff₀ hs0 (by norm_num)]; nlinarith
  have hH2' := abs_le.mp hH2
  have ht : 79 / 10 < t := by linarith
  have hst : 99 / 100 * t ≤ s := by linarith
  have hts : t ≤ 102 / 99 * s := by linarith
  -- L1
  have hA : 33 / 20 / s ^ 3 ≤ 171 / 100 / t ^ 3 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : (99 / 100 * t) ^ 3 ≤ s ^ 3 := pow_le_pow_left₀ (by positivity) hst 3
    nlinarith [pow_pos ht0 3]
  have hB : |5 / (32 * s) - 5 / (32 * t)| ≤ 1 / 10 / t ^ 3 := by
    have e : 5 / (32 * s) - 5 / (32 * t) = 5 * (t - s) / (32 * s * t) := by field_simp
    rw [e, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 32 * s * t), abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 5),
      abs_sub_comm, div_le_div_iff₀ (by positivity) (by positivity)]
    have h3 : |s - t| * s ≤ 3 / 5 := by
      have := mul_le_mul_of_nonneg_right H2 hs0.le
      rwa [div_mul_cancel₀ _ hs0.ne'] at this
    have hs2 : t ^ 2 ≤ (102 / 99) ^ 2 * s ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ ht0.le hts 2
    have : 5 * |s - t| * t ^ 3 ≤ 3 * t ^ 3 / s := by
      calc 5 * |s - t| * t ^ 3 = 5 * (|s - t| * s) * t ^ 3 / s := by field_simp
        _ ≤ 5 * (3 / 5) * t ^ 3 / s := by gcongr
        _ = _ := by ring
    have h4 : 3 * t ^ 3 / s ≤ 1 / 10 * (32 * s * t) := by
      rw [div_le_iff₀ hs0]
      nlinarith [mul_pos ht0 ht0, mul_pos hs0 ht0]
    linarith
  have L1 : |s - t - 5 / (32 * t)| ≤ 181 / 100 / t ^ 3 := by
    have e : s - t - 5 / (32 * t) = (s - t - 5 / (32 * s)) + (5 / (32 * s) - 5 / (32 * t)) := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    have : 181 / 100 / t ^ 3 = 171 / 100 / t ^ 3 + 1 / 10 / t ^ 3 := by ring
    rw [this]
    exact add_le_add (H1.trans hA) hB
  -- the comparison point
  set ĝ := g + 5 / (96 * g ^ 5) with hĝ
  have hĝ0 : g ≤ ĝ := by
    rw [hĝ]
    have : 0 < 5 / (96 * g ^ 5) := by positivity
    linarith
  have hĝ3 : ĝ ^ 3 - t - 5 / (32 * t) = 75 / (9216 * g ^ 9) + 125 / (884736 * g ^ 15) := by
    rw [hĝ, htdef]; field_simp; ring
  have hg6 : 62 < g ^ 6 := by
    have : t ^ 2 = g ^ 6 := by rw [htdef]; ring
    nlinarith
  have hp : 75 / (9216 * g ^ 9) + 125 / (884736 * g ^ 15) ≤ 1 / 100 / t ^ 3 := by
    have e9 : t ^ 3 = g ^ 9 := by rw [htdef]; ring
    rw [e9]
    have e15 : g ^ 15 = g ^ 9 * g ^ 6 := by ring
    rw [e15]
    have hg9 : 0 < g ^ 9 := by positivity
    rw [div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos hg9 hg9, mul_pos (mul_pos hg9 hg9) (by linarith : (0 : ℝ) < g ^ 6 - 62)]
  have hp0 : 0 ≤ 75 / (9216 * g ^ 9) + 125 / (884736 * g ^ 15) := by positivity
  have hq : |ĝ ^ 3 - t - 5 / (32 * t)| ≤ 1 / 100 / t ^ 3 := by
    rw [hĝ3, abs_of_nonneg hp0]; exact hp
  have L2 : |s - ĝ ^ 3| ≤ 182 / 100 / t ^ 3 := by
    calc |s - ĝ ^ 3| = |(s - t - 5 / (32 * t)) - (ĝ ^ 3 - t - 5 / (32 * t))| := by congr 1; ring
      _ ≤ |s - t - 5 / (32 * t)| + |ĝ ^ 3 - t - 5 / (32 * t)| := abs_sub _ _
      _ ≤ 181 / 100 / t ^ 3 + 1 / 100 / t ^ 3 := add_le_add L1 hq
      _ = 182 / 100 / t ^ 3 := by ring
  -- r ≥ 0.99 g
  have hrg : 99 / 100 * g ≤ r := by
    refine le_of_pow_le_pow_left₀ (by norm_num : 3 ≠ 0) hr0.le ?_
    rw [mul_pow, ← hsdef]
    have : (99 / 100 : ℝ) ^ 3 * g ^ 3 ≤ 99 / 100 * t := by
      rw [← htdef]; nlinarith [ht0]
    linarith
  have hĝpos : 0 < ĝ := by linarith
  have hmin : 99 / 100 * g ≤ min r ĝ := le_min hrg (by linarith)
  have hM := airyMin_lemma hr0 hĝpos
  have hM2 : |r ^ 2 - ĝ ^ 2| * (99 / 100 * g) ≤ 182 / 100 / t ^ 3 := by
    calc _ ≤ |r ^ 2 - ĝ ^ 2| * min r ĝ := mul_le_mul_of_nonneg_left hmin (abs_nonneg _)
      _ ≤ |r ^ 3 - ĝ ^ 3| := hM
      _ ≤ _ := L2
  have e9 : t ^ 3 = g ^ 9 := by rw [htdef]; ring
  have hM3 : |r ^ 2 - ĝ ^ 2| ≤ 182 / 99 / g ^ 10 := by
    rw [e9] at hM2
    have hg9 : 0 < g ^ 9 := by positivity
    have : |r ^ 2 - ĝ ^ 2| * (99 / 100 * g * g ^ 9) ≤ 182 / 100 := by
      have := mul_le_mul_of_nonneg_right hM2 hg9.le
      rwa [div_mul_cancel₀ _ hg9.ne', mul_assoc] at this
    rw [le_div_iff₀ (by positivity)]
    have e : g ^ 10 = g * g ^ 9 := by ring
    rw [e]
    nlinarith
  have hfin : ĝ ^ 2 - g ^ 2 - 5 / (48 * g ^ 4) = 25 / (9216 * g ^ 10) := by
    rw [hĝ]; field_simp; ring
  have e : r ^ 2 - g ^ 2 - 5 / (48 * g ^ 4) = (r ^ 2 - ĝ ^ 2) + (ĝ ^ 2 - g ^ 2 - 5 / (48 * g ^ 4)) := by ring
  rw [e, hfin]
  refine (abs_add_le _ _).trans ?_
  rw [abs_of_pos (by positivity : (0 : ℝ) < 25 / (9216 * g ^ 10))]
  have hg10 : 0 < g ^ 10 := by positivity
  calc _ ≤ 182 / 99 / g ^ 10 + 25 / (9216 * g ^ 10) := add_le_add hM3 le_rfl
    _ = (182 / 99 + 25 / 9216) / g ^ 10 := by ring
    _ ≤ 2 / g ^ 10 := by gcongr; norm_num

/-- The argument of DLMF 9.9.18: `t_n = (3π/2)(n - 1/4) = (3π/8)(4n - 1)`. -/
noncomputable def airyZeroT (n : ℕ) : ℝ := 3 * π / 2 * ((n : ℝ) - 1 / 4)

lemma airyZeroT_pos {n : ℕ} (hn : 1 ≤ n) : 0 < airyZeroT n := by
  have : (1 : ℝ) ≤ n := by exact_mod_cast hn
  unfold airyZeroT; nlinarith [Real.pi_pos]

lemma airyZeroT_ge {n : ℕ} (hn : 1 ≤ n) : (n : ℝ) ≤ airyZeroT n := by
  have : (1 : ℝ) ≤ n := by exact_mod_cast hn
  unfold airyZeroT; nlinarith [Real.pi_gt_three]

/-- Cube-root bookkeeping: `g = t^{1/3}` has `g³ = t`, `t^{2/3} = g²`, `t^{-4/3} = 1/g⁴`, `t^{-10/3} = 1/g^{10}`. -/
lemma airySO_rpow {t : ℝ} (ht : 0 < t) :
    (t ^ (1 / 3 : ℝ)) ^ 3 = t ∧ t ^ (2 / 3 : ℝ) = (t ^ (1 / 3 : ℝ)) ^ 2 ∧
      t ^ (-(4 / 3) : ℝ) = 1 / (t ^ (1 / 3 : ℝ)) ^ 4 ∧ t ^ (-(10 / 3) : ℝ) = 1 / (t ^ (1 / 3 : ℝ)) ^ 10 := by
  have key : ∀ k : ℕ, (t ^ (1 / 3 : ℝ)) ^ k = t ^ ((k : ℝ) / 3) := by
    intro k
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    congr 1; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [key 3]; norm_num
  · rw [key 2]; norm_num
  · rw [key 4, one_div, ← Real.rpow_neg ht.le]; norm_num
  · rw [key 10, one_div, ← Real.rpow_neg ht.le]; norm_num

/-- **DLMF 9.9.18, second order, explicit constant.** For `n ≥ 2` and `t = (3π/2)(n - 1/4)`,
`|a_n + t^{2/3} (1 + 5/(48 t²))| ≤ 2 t^{-10/3}`. -/
theorem airyZero_second_order {n : ℕ} (hn : 2 ≤ n) :
    |airyZero n + airyZeroT n ^ (2 / 3 : ℝ) * (1 + 5 / (48 * airyZeroT n ^ 2))| ≤
      2 * airyZeroT n ^ (-(10 / 3) : ℝ) := by
  have ht0 := airyZeroT_pos (by omega : 1 ≤ n)
  obtain ⟨hw3, hw2, -, hw10⟩ := airySO_rpow ht0
  set t := airyZeroT n with htdef
  set g := t ^ (1 / 3 : ℝ) with hgdef
  have hg0 : 0 < g := Real.rpow_pos_of_pos ht0 _
  set r := airyZeroRoot n with hr
  have hr2 : 2 < r := two_lt_airyZeroRoot hn
  have hr0 : 0 < r := by linarith
  have hr3 : 0 < r ^ 3 := by positivity
  have hp := airyZero_phase_second hn
  have hp0 := airyZero_phase_r hn
  rw [← hr] at hp hp0
  have ht : t = 3 * π / 2 * ((n : ℝ) - 1 / 4) := rfl
  have H1 : |r ^ 3 - g ^ 3 - 5 / (32 * r ^ 3)| ≤ 33 / 20 / (r ^ 3) ^ 3 := by
    have e : r ^ 3 - g ^ 3 - 5 / (32 * r ^ 3) =
        3 / 2 * (2 / 3 * r ^ 3 - ((n : ℝ) - 1 / 4) * π - 5 / (48 * r ^ 3)) := by
      rw [hw3, ht]; field_simp; ring
    rw [e, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]
    have e9 : (r ^ 3) ^ 3 = r ^ 9 := by ring
    rw [e9]
    calc 3 / 2 * |_| ≤ 3 / 2 * (11 / 10 * (1 / r ^ 9)) := by gcongr
      _ = _ := by ring
  have H2 : |r ^ 3 - g ^ 3| ≤ 3 / 5 / r ^ 3 := by
    have e : r ^ 3 - g ^ 3 = 3 / 2 * (2 / 3 * r ^ 3 - ((n : ℝ) - 1 / 4) * π) := by
      rw [hw3, ht]; ring
    rw [e, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]
    calc 3 / 2 * |_| ≤ 3 / 2 * (2 / 5 / r ^ 3) := by gcongr
      _ = _ := by ring
  have hI := airySO_invert hr2 hg0 H1 H2
  rw [hw2, hw10, airyZero_eq_neg_root_sq n, ← hr]
  have ht2 : t ^ 2 = g ^ 6 := by rw [← hw3]; ring
  have e : -r ^ 2 + g ^ 2 * (1 + 5 / (48 * t ^ 2)) = -(r ^ 2 - g ^ 2 - 5 / (48 * g ^ 4)) := by
    rw [ht2]; field_simp; ring
  rw [e, abs_neg]
  calc _ ≤ 2 / g ^ 10 := hI
    _ = _ := by ring

/-- `|a_n + t^{2/3}(1 + 5/(48 t²))| ≤ 2 n^{-10/3}` for `n ≥ 2`. -/
theorem airyZero_second_order_n {n : ℕ} (hn : 2 ≤ n) :
    |airyZero n + airyZeroT n ^ (2 / 3 : ℝ) * (1 + 5 / (48 * airyZeroT n ^ 2))| ≤
      2 * (n : ℝ) ^ (-(10 / 3) : ℝ) := by
  refine (airyZero_second_order hn).trans ?_
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have := Real.rpow_le_rpow_of_nonpos hn0 (airyZeroT_ge (by omega : 1 ≤ n)) (by norm_num : (-(10 / 3) : ℝ) ≤ 0)
  linarith

/-- **The deviation of `a_n` from the leading Weyl value, with its second-order term**: for `n ≥ 2`,
`|a_n + t^{2/3} + (5/48) t^{-4/3}| ≤ 2 t^{-10/3}`, i.e. `δ_n = -(5/48) t_n^{-4/3} (1 + O(t_n^{-2}))`. -/
theorem airyZero_delta_second {n : ℕ} (hn : 2 ≤ n) :
    |airyZero n + airyZeroT n ^ (2 / 3 : ℝ) + 5 / 48 * airyZeroT n ^ (-(4 / 3) : ℝ)| ≤
      2 * airyZeroT n ^ (-(10 / 3) : ℝ) := by
  have ht0 := airyZeroT_pos (by omega : 1 ≤ n)
  obtain ⟨hw3, hw2, hw4, -⟩ := airySO_rpow ht0
  have h := airyZero_second_order hn
  set t := airyZeroT n
  set g := t ^ (1 / 3 : ℝ)
  have hg0 : 0 < g := Real.rpow_pos_of_pos ht0 _
  have ht2 : t ^ 2 = g ^ 6 := by rw [← hw3]; ring
  have e : airyZero n + t ^ (2 / 3 : ℝ) + 5 / 48 * t ^ (-(4 / 3) : ℝ) =
      airyZero n + t ^ (2 / 3 : ℝ) * (1 + 5 / (48 * t ^ 2)) := by
    rw [hw2, hw4, ht2]; field_simp; ring
  rw [e]; exact h

/-- **Lemma Z (all `n ≥ 1`)**: there is `C` with `|a_n + t_n^{2/3}| ≤ C n^{-4/3}` for every `n ≥ 1`
(`n ≥ 2` is `airyZero_delta` with `C = 0.1`; `n = 1` is absorbed in the constant). -/
theorem airyZero_delta_exists :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → |airyZero n + airyZeroT n ^ (2 / 3 : ℝ)| ≤ C * (n : ℝ) ^ (-(4 / 3) : ℝ) := by
  refine ⟨max (1 / 10) (|airyZero 1 + airyZeroT 1 ^ (2 / 3 : ℝ)|), fun n hn => ?_⟩
  rcases hn.eq_or_lt with rfl | h2
  · simp only [Nat.cast_one, Real.one_rpow, mul_one]
    exact le_max_right _ _
  · have := airyZero_delta (n := n) h2
    refine this.trans ?_
    have hp : 0 < (n : ℝ) ^ (-(4 / 3) : ℝ) := Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < n)) _
    have : (0.1 : ℝ) ≤ max (1 / 10) (|airyZero 1 + airyZeroT 1 ^ (2 / 3 : ℝ)|) := by
      have := le_max_left (1 / 10 : ℝ) (|airyZero 1 + airyZeroT 1 ^ (2 / 3 : ℝ)|)
      norm_num at this ⊢
    nlinarith

/-- **Second order, all `n ≥ 1`**: there is `C` with
`|a_n + t_n^{2/3}(1 + 5/(48 t_n²))| ≤ C t_n^{-10/3}` for every `n ≥ 1`. -/
theorem airyZero_second_order_exists :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      |airyZero n + airyZeroT n ^ (2 / 3 : ℝ) * (1 + 5 / (48 * airyZeroT n ^ 2))| ≤
        C * airyZeroT n ^ (-(10 / 3) : ℝ) := by
  refine ⟨max 2 (|airyZero 1 + airyZeroT 1 ^ (2 / 3 : ℝ) * (1 + 5 / (48 * airyZeroT 1 ^ 2))| /
    airyZeroT 1 ^ (-(10 / 3) : ℝ)), fun n hn => ?_⟩
  rcases hn.eq_or_lt with rfl | h2
  · have hp : 0 < airyZeroT 1 ^ (-(10 / 3) : ℝ) := Real.rpow_pos_of_pos (airyZeroT_pos le_rfl) _
    rw [← div_le_iff₀ hp]
    exact le_max_right _ _
  · have hp : 0 < airyZeroT n ^ (-(10 / 3) : ℝ) := Real.rpow_pos_of_pos (airyZeroT_pos (by omega)) _
    refine (airyZero_second_order h2).trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hp.le

/-- info: 'FormalResearch.Special.airySO_invert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airySO_invert

/-- info: 'FormalResearch.Special.airyZero_second_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyZero_second_order

/-- info: 'FormalResearch.Special.airyZero_second_order_n' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyZero_second_order_n

/-- info: 'FormalResearch.Special.airyZero_delta_second' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyZero_delta_second

/-- info: 'FormalResearch.Special.airyZero_delta_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyZero_delta_exists

/-- info: 'FormalResearch.Special.airyZero_second_order_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyZero_second_order_exists

end FormalResearch.Special
