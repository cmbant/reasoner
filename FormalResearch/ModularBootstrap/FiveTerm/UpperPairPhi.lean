module

public import Mathlib

/-!
# Pair-drift cancellation for symmetric `+m`, `-m` sites (FIVE-U; `cts:tip-shared` (b1), analytic core)

Source: `CFT/modular_bootstrap/paper/constant_term_slit_strip.tex`, Lemma C11$_0$ (`cts:tip-shared`) (b1),
proof ("the odd `O(m/n)` drift of the spacings and of the weights cancels in the pairs `k = n ± m`").

Everything proved here is an exact inequality with explicit constants (`∃ C n₁` depending only on the
structural constants `K, c, c₀`), uniform in all remaining parameters:

* `log_one_add_sub_le`: `|log(1+e) - e| ≤ 2 e²` for `|e| ≤ 1/2`;
* `pair_one_sided`: moving a site `u₀ → u₁ = u₀ + κ' m²/2 + r` and a weight `W₀ → W₁ = W₀(1+bm+ρ)` changes
  `log(1 + W/u²)` by the explicit first-order term up to `O(W_b/n²)`;
* `pair_cancel`: for the symmetric pair `±m` the first-order terms cancel to `O(W_b/(n m²))`, so the pair error
  is `O(W_b (1/(n m²) + 1/n²))`.

All statements are proved (no numerical input).
-/

@[expose] public section

open Set

namespace FormalResearch.ModularBootstrap.FiveTerm

lemma log_one_add_sub_le {e : ℝ} (he : |e| ≤ 1 / 2) : |Real.log (1 + e) - e| ≤ 2 * e ^ 2 := by
  have h1 : |(-e)| < 1 := by rw [abs_neg]; linarith
  have := Real.abs_log_sub_add_sum_range_le h1 1
  simp only [Finset.sum_range_one, pow_one, zero_add, Nat.cast_zero, div_one, abs_neg] at this
  have h2 : Real.log (1 - -e) = Real.log (1 + e) := by ring_nf
  rw [h2, show -e + Real.log (1 + e) = Real.log (1 + e) - e by ring] at this
  have h4 : (1 : ℝ) / 2 ≤ 1 - |e| := by linarith
  calc |Real.log (1 + e) - e| ≤ |e| ^ (1 + 1) / (1 - |e|) := this
    _ ≤ 2 * e ^ 2 := by
        rw [div_le_iff₀ (by linarith), pow_two |e|, abs_mul_abs_self]
        nlinarith only [h4, sq_nonneg e]


lemma inv_sq_taylor {u0 u1 : ℝ} (h0 : 0 < u0) (h1 : 0 < u1) :
    1 / u1 ^ 2 - 1 / u0 ^ 2 + 2 * (u1 - u0) / u0 ^ 3 =
      (u1 - u0) ^ 2 * (u0 + 2 * u1) / (u0 ^ 3 * u1 ^ 2) := by
  field_simp
  ring

lemma inv_sq_taylor_le {u0 u1 ρ : ℝ} (hρ : 0 < ρ) (h0 : ρ ≤ u0) (h1 : ρ ≤ u1) :
    |1 / u1 ^ 2 - 1 / u0 ^ 2 + 2 * (u1 - u0) / u0 ^ 3| ≤ 3 * (u1 - u0) ^ 2 / ρ ^ 4 := by
  have hu0 : 0 < u0 := hρ.trans_le h0
  have hu1 : 0 < u1 := hρ.trans_le h1
  rw [inv_sq_taylor hu0 hu1, abs_of_nonneg (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
  have e1 : ρ ^ 4 ≤ u0 ^ 2 * u1 ^ 2 := by
    have := mul_le_mul (pow_le_pow_left₀ hρ.le h0 2) (pow_le_pow_left₀ hρ.le h1 2) (by positivity) (by positivity)
    nlinarith only [this]
  have e2 : ρ ^ 4 * u1 ≤ u0 ^ 3 * u1 ^ 2 := by
    have h3 : ρ ^ 3 ≤ u0 ^ 3 := pow_le_pow_left₀ hρ.le h0 3
    have h4 : ρ ≤ u1 := h1
    nlinarith only [mul_le_mul h3 h4 hρ.le (by positivity), e1, hu1, h3]
  have key : (u0 + 2 * u1) * ρ ^ 4 ≤ 3 * (u0 ^ 3 * u1 ^ 2) := by
    nlinarith only [mul_le_mul_of_nonneg_left e1 hu0.le, e2]
  have := mul_le_mul_of_nonneg_left key (sq_nonneg (u1 - u0))
  nlinarith only [this]

lemma inv_sq_diff_le {m n K c u0 u1 r k : ℝ} (hm : 1 ≤ m) (hn : 2 * m ≤ n) (hK : 1 ≤ K) (hc : 0 < c)
    (hu0 : m / 4 ≤ u0) (hu0' : u0 ≤ 2 * m) (hu1 : u1 = u0 + k * m ^ 2 / 2 + r) (hcu : c * m ≤ u1)
    (hc4 : c ≤ 1 / 4) (hk : |k| ≤ K / n) (hr : |r| ≤ K * m ^ 3 / n ^ 2) :
    |u1 - u0| ≤ K * m ^ 2 / n ∧ |1 / u1 ^ 2 - 1 / u0 ^ 2| ≤ 16 * K * (4 + K / 2) / c ^ 2 / (n * m) := by
  have hn0 : 0 < n := by linarith
  have hm0 : 0 < m := by linarith
  have hd : |u1 - u0| ≤ K * m ^ 2 / n := by
    have : u1 - u0 = k * m ^ 2 / 2 + r := by rw [hu1]; ring
    rw [this]
    have h1 : |k * m ^ 2 / 2| ≤ K / n * m ^ 2 / 2 := by
      rw [abs_div, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ m ^ 2), abs_two]
      have := mul_le_mul_of_nonneg_right hk (by positivity : (0:ℝ) ≤ m ^ 2)
      linarith
    have h2 : K * m ^ 3 / n ^ 2 ≤ K * m ^ 2 / (2 * n) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : 0 ≤ K * m ^ 2 * n := by positivity
      nlinarith only [mul_le_mul_of_nonneg_left hn this]
    calc |k * m ^ 2 / 2 + r| ≤ |k * m ^ 2 / 2| + |r| := abs_add_le _ _
      _ ≤ K / n * m ^ 2 / 2 + K * m ^ 2 / (2 * n) := add_le_add h1 (hr.trans h2)
      _ = K * m ^ 2 / n := by field_simp; ring
  refine ⟨hd, ?_⟩
  have hu1p : 0 < u1 := by nlinarith only [hcu, hm0, hc]
  have hu0p : 0 < u0 := by linarith
  have hid : 1 / u1 ^ 2 - 1 / u0 ^ 2 = (u0 - u1) * (u0 + u1) / (u0 ^ 2 * u1 ^ 2) := by
    field_simp; ring
  rw [hid, abs_div, abs_mul, abs_of_pos (by positivity : 0 < u0 ^ 2 * u1 ^ 2), abs_sub_comm]
  have hsum : |u0 + u1| ≤ (4 + K / 2) * m := by
    rw [abs_of_pos (by linarith)]
    have : u1 ≤ u0 + K * m ^ 2 / n := by linarith [(abs_le.mp hd).2]
    have h5 : K * m ^ 2 / n ≤ K * m / 2 := by
      rw [div_le_iff₀ (by linarith)]; nlinarith only [mul_le_mul_of_nonneg_left hn (by positivity : 0 ≤ K * m)]
    nlinarith only [this, h5, hu0']
  have hden : c ^ 2 * m ^ 4 / 16 ≤ u0 ^ 2 * u1 ^ 2 := by
    have h6 : (m / 4) ^ 2 * (c * m) ^ 2 ≤ u0 ^ 2 * u1 ^ 2 :=
      mul_le_mul (pow_le_pow_left₀ (by positivity) hu0 2) (pow_le_pow_left₀ (by positivity) hcu 2)
        (by positivity) (by positivity)
    nlinarith only [h6]
  have hnum : |u1 - u0| * |u0 + u1| ≤ (K * m ^ 2 / n) * ((4 + K / 2) * m) :=
    mul_le_mul hd hsum (abs_nonneg _) (by positivity)
  calc |u1 - u0| * |u0 + u1| / (u0 ^ 2 * u1 ^ 2) ≤ (K * m ^ 2 / n) * ((4 + K / 2) * m) / (c ^ 2 * m ^ 4 / 16) := by
        apply div_le_div₀ (by positivity) hnum (by positivity) hden
    _ = 16 * K * (4 + K / 2) / c ^ 2 / (n * m) := by field_simp


/-- The one-sided expansion: moving the site `u0` to `u1` and the weight `W0` to `W1` changes
`log(1+W/u²)` by the explicit first-order terms, up to `O(Wb/n²)`. -/
lemma pair_one_sided {K c c0 : ℝ} (hK : 1 ≤ K) (hc : 0 < c) (hc4 : c ≤ 1 / 4) (hc0 : 1 ≤ c0) :
    ∃ C n1 : ℝ, 0 ≤ C ∧ ∀ (m n u0 u1 W0 W1 b k r ρ Wb : ℝ), 1 ≤ m → 2 * m ≤ n → n1 ≤ n →
      m / 4 ≤ u0 → u0 ≤ 2 * m → u1 = u0 + k * m ^ 2 / 2 + r → c * m ≤ u1 →
      W1 = W0 * (1 + b * m + ρ) → 0 ≤ W0 → W0 ≤ Wb → Wb ≤ c0 → 0 ≤ W1 →
      |b| ≤ K / n → |k| ≤ K / n → |r| ≤ K * m ^ 3 / n ^ 2 → |ρ| ≤ K * m ^ 2 / n ^ 2 →
      |Real.log (1 + W1 / u1 ^ 2) - Real.log (1 + W0 / u0 ^ 2) -
        (W0 * b * m / (u0 ^ 2 + W0) - k * m ^ 2 * W0 / (u0 * (u0 ^ 2 + W0)))| ≤ C * Wb / n ^ 2 := by
  set Q1 : ℝ := 16 * K * (4 + K / 2) / c ^ 2 with hQ1
  set Q2 : ℝ := 3 * K / (2 * c ^ 2) + Q1 with hQ2
  set Q3 : ℝ := K / c ^ 2 + K * Q1 + 3 * K ^ 2 / c ^ 4 + 128 * K with hQ3
  have hQ1p : 0 ≤ Q1 := by positivity
  have hQ2p : 0 ≤ Q2 := by positivity
  have hQ3p : 0 ≤ Q3 := by positivity
  refine ⟨2 * Q2 ^ 2 * c0 + Q3, 2 * Q2 * c0, by positivity, ?_⟩
  intro m n u0 u1 W0 W1 b k r ρ Wb hm hn hn1 hu0 hu0' hu1 hcu hW1 hW0 hW0b hWbc hW1p hb hk hr hρ
  have hn0 : 0 < n := by linarith
  have hm0 : 0 < m := by linarith
  have hu0p : 0 < u0 := by linarith
  have hu1p : 0 < u1 := by nlinarith only [hcu, hm0, hc]
  obtain ⟨hd, hQ⟩ := inv_sq_diff_le hm hn hK hc hu0 hu0' hu1 hcu hc4 hk hr
  have hWb0 : 0 ≤ Wb := hW0.trans hW0b
  -- the z-increment
  have hbm : |b * m + ρ| ≤ 3 * K * m / (2 * n) := by
    have h1 : |b * m| ≤ K * m / n := by
      rw [abs_mul, abs_of_pos hm0]
      calc |b| * m ≤ K / n * m := mul_le_mul_of_nonneg_right hb hm0.le
        _ = K * m / n := by ring
    have h2 : |ρ| ≤ K * m / (2 * n) := by
      refine hρ.trans ?_
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith only [mul_le_mul_of_nonneg_left hn (by positivity : 0 ≤ K * m * n)]
    calc |b * m + ρ| ≤ |b * m| + |ρ| := abs_add_le _ _
      _ ≤ K * m / n + K * m / (2 * n) := add_le_add h1 h2
      _ = 3 * K * m / (2 * n) := by field_simp; ring
  have hA : |(W1 - W0) / u1 ^ 2| ≤ 3 * K / (2 * c ^ 2) * Wb / (n * m) := by
    have hW10 : W1 - W0 = W0 * (b * m + ρ) := by rw [hW1]; ring
    rw [hW10, abs_div, abs_mul, abs_of_nonneg hW0, abs_of_pos (by positivity : 0 < u1 ^ 2)]
    have hu1sq : c ^ 2 * m ^ 2 ≤ u1 ^ 2 := by
      have := pow_le_pow_left₀ (by positivity) hcu 2
      nlinarith only [this]
    calc W0 * |b * m + ρ| / u1 ^ 2 ≤ Wb * (3 * K * m / (2 * n)) / (c ^ 2 * m ^ 2) := by
          apply div_le_div₀ (by positivity) (mul_le_mul hW0b hbm (abs_nonneg _) hWb0) (by positivity) hu1sq
      _ = 3 * K / (2 * c ^ 2) * Wb / (n * m) := by field_simp
  have hB : |W0 * (1 / u1 ^ 2 - 1 / u0 ^ 2)| ≤ Q1 * Wb / (n * m) := by
    rw [abs_mul, abs_of_nonneg hW0]
    calc W0 * |1 / u1 ^ 2 - 1 / u0 ^ 2| ≤ Wb * (Q1 / (n * m)) :=
          mul_le_mul hW0b hQ (abs_nonneg _) hWb0
      _ = Q1 * Wb / (n * m) := by ring
  have hz : |W1 / u1 ^ 2 - W0 / u0 ^ 2| ≤ Q2 * Wb / (n * m) := by
    have : W1 / u1 ^ 2 - W0 / u0 ^ 2 = (W1 - W0) / u1 ^ 2 + W0 * (1 / u1 ^ 2 - 1 / u0 ^ 2) := by ring
    rw [this]
    calc _ ≤ |(W1 - W0) / u1 ^ 2| + |W0 * (1 / u1 ^ 2 - 1 / u0 ^ 2)| := abs_add_le _ _
      _ ≤ 3 * K / (2 * c ^ 2) * Wb / (n * m) + Q1 * Wb / (n * m) := add_le_add hA hB
      _ = Q2 * Wb / (n * m) := by rw [hQ2]; ring
  have hzhalf : |W1 / u1 ^ 2 - W0 / u0 ^ 2| ≤ 1 / 2 := by
    refine hz.trans ?_
    rw [div_le_iff₀ (by positivity)]
    have h1 : Q2 * Wb ≤ Q2 * c0 := mul_le_mul_of_nonneg_left hWbc hQ2p
    have h2 : 2 * Q2 * c0 ≤ n := hn1
    have h3 : (1:ℝ) ≤ m := hm
    nlinarith only [h1, h2, mul_le_mul_of_nonneg_left h3 (by positivity : (0:ℝ) ≤ n / 2)]
  -- the remainder after the main term
  have hE2 : 2 * (u1 - u0) = k * m ^ 2 + 2 * r := by rw [hu1]; ring
  have hEid : 1 / u1 ^ 2 - 1 / u0 ^ 2 + 2 * (u1 - u0) / u0 ^ 3 =
      1 / u1 ^ 2 - 1 / u0 ^ 2 + (k * m ^ 2 + 2 * r) / u0 ^ 3 := by rw [hE2]
  have hEb : |1 / u1 ^ 2 - 1 / u0 ^ 2 + 2 * (u1 - u0) / u0 ^ 3| ≤ 3 * K ^ 2 / (c ^ 4 * n ^ 2) := by
    have h := inv_sq_taylor_le (u0 := u0) (u1 := u1) (ρ := c * m) (by positivity)
      (by nlinarith only [hu0, hc4, hm0]) hcu
    refine h.trans ?_
    have h7 : (u1 - u0) ^ 2 ≤ (K * m ^ 2 / n) ^ 2 := by
      have := sq_le_sq' (abs_le.mp hd).1 (abs_le.mp hd).2
      simpa using this
    calc 3 * (u1 - u0) ^ 2 / (c * m) ^ 4 ≤ 3 * (K * m ^ 2 / n) ^ 2 / (c * m) ^ 4 := by
          apply div_le_div_of_nonneg_right (by nlinarith only [h7]) (by positivity)
      _ = 3 * K ^ 2 / (c ^ 4 * n ^ 2) := by field_simp
  have hR : |W1 / u1 ^ 2 - W0 / u0 ^ 2 - (W0 * b * m / u0 ^ 2 - k * m ^ 2 * W0 / u0 ^ 3)| ≤ Q3 * Wb / n ^ 2 := by
    have hid : W1 / u1 ^ 2 - W0 / u0 ^ 2 - (W0 * b * m / u0 ^ 2 - k * m ^ 2 * W0 / u0 ^ 3) =
        W0 * ρ / u1 ^ 2 + W0 * b * m * (1 / u1 ^ 2 - 1 / u0 ^ 2) +
          W0 * ((1 / u1 ^ 2 - 1 / u0 ^ 2 + 2 * (u1 - u0) / u0 ^ 3) - 2 * r / u0 ^ 3) := by
      rw [hEid, hW1]; ring
    rw [hid]
    have t1 : |W0 * ρ / u1 ^ 2| ≤ K / c ^ 2 * Wb / n ^ 2 := by
      have hu1sq : c ^ 2 * m ^ 2 ≤ u1 ^ 2 := by
        have := pow_le_pow_left₀ (by positivity) hcu 2
        nlinarith only [this]
      rw [abs_div, abs_mul, abs_of_nonneg hW0, abs_of_pos (by positivity : 0 < u1 ^ 2)]
      calc W0 * |ρ| / u1 ^ 2 ≤ Wb * (K * m ^ 2 / n ^ 2) / (c ^ 2 * m ^ 2) :=
            div_le_div₀ (by positivity) (mul_le_mul hW0b hρ (abs_nonneg _) hWb0) (by positivity) hu1sq
        _ = K / c ^ 2 * Wb / n ^ 2 := by field_simp
    have t2 : |W0 * b * m * (1 / u1 ^ 2 - 1 / u0 ^ 2)| ≤ K * Q1 * Wb / n ^ 2 := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hW0, abs_of_pos hm0]
      calc W0 * |b| * m * |1 / u1 ^ 2 - 1 / u0 ^ 2| ≤ Wb * (K / n) * m * (Q1 / (n * m)) := by
            gcongr
        _ = K * Q1 * Wb / n ^ 2 := by field_simp
    have t3 : |W0 * ((1 / u1 ^ 2 - 1 / u0 ^ 2 + 2 * (u1 - u0) / u0 ^ 3) - 2 * r / u0 ^ 3)| ≤
        (3 * K ^ 2 / c ^ 4 + 128 * K) * Wb / n ^ 2 := by
      rw [abs_mul, abs_of_nonneg hW0]
      have hr3 : |2 * r / u0 ^ 3| ≤ 128 * K / n ^ 2 := by
        rw [abs_div, abs_mul, abs_of_pos (by positivity : 0 < u0 ^ 3), abs_two]
        have h8 : (m / 4) ^ 3 ≤ u0 ^ 3 := pow_le_pow_left₀ (by positivity) hu0 3
        calc 2 * |r| / u0 ^ 3 ≤ 2 * (K * m ^ 3 / n ^ 2) / (m / 4) ^ 3 :=
              div_le_div₀ (by positivity) (by linarith) (by positivity) h8
          _ = 128 * K / n ^ 2 := by field_simp; norm_num
      have h9 : |(1 / u1 ^ 2 - 1 / u0 ^ 2 + 2 * (u1 - u0) / u0 ^ 3) - 2 * r / u0 ^ 3| ≤
          3 * K ^ 2 / (c ^ 4 * n ^ 2) + 128 * K / n ^ 2 := (abs_sub _ _).trans (add_le_add hEb hr3)
      calc W0 * |_| ≤ Wb * (3 * K ^ 2 / (c ^ 4 * n ^ 2) + 128 * K / n ^ 2) :=
            mul_le_mul hW0b h9 (abs_nonneg _) hWb0
        _ = (3 * K ^ 2 / c ^ 4 + 128 * K) * Wb / n ^ 2 := by field_simp
    calc _ ≤ |W0 * ρ / u1 ^ 2 + W0 * b * m * (1 / u1 ^ 2 - 1 / u0 ^ 2)| +
          |W0 * ((1 / u1 ^ 2 - 1 / u0 ^ 2 + 2 * (u1 - u0) / u0 ^ 3) - 2 * r / u0 ^ 3)| := abs_add_le _ _
      _ ≤ (K / c ^ 2 * Wb / n ^ 2 + K * Q1 * Wb / n ^ 2) + (3 * K ^ 2 / c ^ 4 + 128 * K) * Wb / n ^ 2 :=
          add_le_add ((abs_add_le _ _).trans (add_le_add t1 t2)) t3
      _ = Q3 * Wb / n ^ 2 := by rw [hQ3]; ring
  -- final: the logarithm step
  set z0 : ℝ := W0 / u0 ^ 2 with hz0
  set z1 : ℝ := W1 / u1 ^ 2 with hz1
  have hz0p : 0 ≤ z0 := by positivity
  have hz1p : 0 ≤ z1 := by positivity
  set X : ℝ := W0 * b * m / u0 ^ 2 - k * m ^ 2 * W0 / u0 ^ 3 with hX
  have h1z0 : 0 < 1 + z0 := by linarith
  set e : ℝ := (z1 - z0) / (1 + z0) with he
  have hed : |e| ≤ |z1 - z0| := by
    rw [he, abs_div, abs_of_pos h1z0]
    exact div_le_self (abs_nonneg _) (by linarith)
  have he12 : |e| ≤ 1 / 2 := hed.trans hzhalf
  have hlog : Real.log (1 + z1) - Real.log (1 + z0) = Real.log (1 + e) := by
    have h : 1 + z1 = (1 + z0) * (1 + e) := by rw [he]; field_simp; ring
    rw [h, Real.log_mul h1z0.ne' (by linarith [abs_le.mp he12])]; ring
  have hM : W0 * b * m / (u0 ^ 2 + W0) - k * m ^ 2 * W0 / (u0 * (u0 ^ 2 + W0)) = X / (1 + z0) := by
    rw [hX, hz0]; field_simp
  have h2 : |Real.log (1 + e) - e| ≤ 2 * e ^ 2 := log_one_add_sub_le he12
  have h3 : |e - X / (1 + z0)| ≤ Q3 * Wb / n ^ 2 := by
    have : e - X / (1 + z0) = (z1 - z0 - X) / (1 + z0) := by rw [he]; ring
    rw [this, abs_div, abs_of_pos h1z0]
    refine (div_le_self (abs_nonneg _) (by linarith)).trans hR
  have h4 : 2 * e ^ 2 ≤ 2 * Q2 ^ 2 * c0 * Wb / n ^ 2 := by
    have h5 : |e| ≤ Q2 * Wb / (n * m) := hed.trans hz
    have h6 : e ^ 2 ≤ (Q2 * Wb / (n * m)) ^ 2 := by
      have := sq_le_sq' (abs_le.mp h5).1 (abs_le.mp h5).2
      exact this
    calc 2 * e ^ 2 ≤ 2 * (Q2 * Wb / (n * m)) ^ 2 := by linarith
      _ = 2 * Q2 ^ 2 * Wb * Wb / (n ^ 2 * m ^ 2) := by field_simp
      _ ≤ 2 * Q2 ^ 2 * c0 * Wb / n ^ 2 := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have h7 : Wb ≤ c0 := hWbc
          have h8 : (1 : ℝ) ≤ m ^ 2 := by nlinarith only [hm]
          have h9 : 0 ≤ 2 * Q2 ^ 2 * Wb * n ^ 2 := by positivity
          nlinarith only [mul_le_mul_of_nonneg_left h7 (by positivity : 0 ≤ 2 * Q2 ^ 2 * Wb * n ^ 2),
            mul_le_mul_of_nonneg_left h8 (by positivity : 0 ≤ 2 * Q2 ^ 2 * c0 * Wb * n ^ 2)]
  rw [hM, show Real.log (1 + z1) - Real.log (1 + z0) - X / (1 + z0) =
    (Real.log (1 + e) - e) + (e - X / (1 + z0)) by rw [hlog]; ring]
  calc _ ≤ |Real.log (1 + e) - e| + |e - X / (1 + z0)| := abs_add_le _ _
    _ ≤ 2 * Q2 ^ 2 * c0 * Wb / n ^ 2 + Q3 * Wb / n ^ 2 := add_le_add (h2.trans h4) h3
    _ = (2 * Q2 ^ 2 * c0 + Q3) * Wb / n ^ 2 := by ring



/-- The `±m` pair cancellation: the odd `O(m/n)` drifts of the spacings and of the weights cancel. -/
lemma pair_cancel {K c c0 : ℝ} (hK : 1 ≤ K) (hc : 0 < c) (hc4 : c ≤ 1 / 4) (hc0 : 1 ≤ c0) :
    ∃ C n1 : ℝ, 0 ≤ C ∧ ∀ (m n ς W0 W1 W2 b k r1 r2 ρ1 ρ2 Wb u1 u2 : ℝ), 1 ≤ m → 2 * m ≤ n → n1 ≤ n →
      |ς| ≤ 3 / 4 →
      u1 = (m + ς) + k * m ^ 2 / 2 + r1 → c * m ≤ u1 →
      u2 = (m - ς) + (-k) * m ^ 2 / 2 + (-r2) → c * m ≤ u2 →
      W1 = W0 * (1 + b * m + ρ1) → W2 = W0 * (1 + (-b) * m + ρ2) → 0 ≤ W0 → W0 ≤ Wb → Wb ≤ c0 →
      0 ≤ W1 → 0 ≤ W2 → |b| ≤ K / n → |k| ≤ K / n → |r1| ≤ K * m ^ 3 / n ^ 2 → |r2| ≤ K * m ^ 3 / n ^ 2 →
      |ρ1| ≤ K * m ^ 2 / n ^ 2 → |ρ2| ≤ K * m ^ 2 / n ^ 2 →
      |(Real.log (1 + W1 / u1 ^ 2) + Real.log (1 + W2 / u2 ^ 2)) -
        (Real.log (1 + W0 / (m + ς) ^ 2) + Real.log (1 + W0 / (m - ς) ^ 2))| ≤
        C * Wb * (1 / (n * m ^ 2) + 1 / n ^ 2) := by
  obtain ⟨CL, n1, hCL, hL⟩ := pair_one_sided (K := K) (c := c) (c0 := c0) hK hc hc4 hc0
  refine ⟨2 * CL + K * (768 + 24576 * (4 + c0)), n1, by positivity, ?_⟩
  intro m n ς W0 W1 W2 b k r1 r2 ρ1 ρ2 Wb u1 u2 hm hn hn1 hς hu1 hcu1 hu2 hcu2 hW1 hW2 hW0 hW0b hWbc hW1p
    hW2p hb hk hr1 hr2 hρ1 hρ2
  have hn0 : 0 < n := by linarith
  have hm0 : 0 < m := by linarith
  have hς' := abs_le.mp hς
  have hu0 : m / 4 ≤ m + ς := by linarith
  have hu0' : m + ς ≤ 2 * m := by linarith
  have hv0 : m / 4 ≤ m - ς := by linarith
  have hv0' : m - ς ≤ 2 * m := by linarith
  have hWb0 : 0 ≤ Wb := hW0.trans hW0b
  have A1 := hL m n (m + ς) u1 W0 W1 b k r1 ρ1 Wb hm hn hn1 hu0 hu0' hu1 hcu1 hW1 hW0 hW0b hWbc hW1p hb hk hr1 hρ1
  have A2 := hL m n (m - ς) u2 W0 W2 (-b) (-k) (-r2) ρ2 Wb hm hn hn1 hv0 hv0' hu2 hcu2 hW2 hW0 hW0b hWbc hW2p
    (by rwa [abs_neg]) (by rwa [abs_neg]) (by rwa [abs_neg]) hρ2
  set M1 : ℝ := W0 * b * m / ((m + ς) ^ 2 + W0) - k * m ^ 2 * W0 / ((m + ς) * ((m + ς) ^ 2 + W0)) with hM1
  set M2 : ℝ := W0 * (-b) * m / ((m - ς) ^ 2 + W0) - (-k) * m ^ 2 * W0 / ((m - ς) * ((m - ς) ^ 2 + W0)) with hM2
  have hu0p : 0 < m + ς := by linarith
  have hv0p : 0 < m - ς := by linarith
  -- the main terms cancel to second order
  have hg1 : |1 / ((m + ς) ^ 2 + W0) - 1 / ((m - ς) ^ 2 + W0)| ≤ 768 / m ^ 3 := by
    have hid : 1 / ((m + ς) ^ 2 + W0) - 1 / ((m - ς) ^ 2 + W0) =
        -(4 * ς * m) / (((m + ς) ^ 2 + W0) * ((m - ς) ^ 2 + W0)) := by
      field_simp; ring
    rw [hid, abs_div, abs_neg, abs_of_pos (by positivity : 0 < ((m + ς) ^ 2 + W0) * ((m - ς) ^ 2 + W0)),
      abs_mul, abs_mul, abs_of_pos hm0]
    have hd : m ^ 4 / 256 ≤ ((m + ς) ^ 2 + W0) * ((m - ς) ^ 2 + W0) := by
      have h1 : (m / 4) ^ 2 ≤ (m + ς) ^ 2 + W0 := by nlinarith only [hu0, hW0, hm0]
      have h2 : (m / 4) ^ 2 ≤ (m - ς) ^ 2 + W0 := by nlinarith only [hv0, hW0, hm0]
      have := mul_le_mul h1 h2 (by positivity) (by positivity)
      nlinarith only [this]
    calc |4| * |ς| * m / _ ≤ 4 * (3 / 4) * m / (m ^ 4 / 256) := by
          apply div_le_div₀ (by positivity) _ (by positivity) hd
          rw [abs_of_pos (by norm_num : (0:ℝ) < 4)]
          have := mul_le_mul_of_nonneg_left hς (by norm_num : (0:ℝ) ≤ 4)
          nlinarith only [this, hm0]
      _ = 768 / m ^ 3 := by field_simp; norm_num
  have hg2 : |1 / ((m + ς) * ((m + ς) ^ 2 + W0)) - 1 / ((m - ς) * ((m - ς) ^ 2 + W0))| ≤
      24576 * (4 + c0) / m ^ 4 := by
    have hid : 1 / ((m + ς) * ((m + ς) ^ 2 + W0)) - 1 / ((m - ς) * ((m - ς) ^ 2 + W0)) =
        -(2 * ς * (((m + ς) ^ 2 + (m + ς) * (m - ς) + (m - ς) ^ 2) + W0)) /
          (((m + ς) * ((m + ς) ^ 2 + W0)) * ((m - ς) * ((m - ς) ^ 2 + W0))) := by
      field_simp; ring
    rw [hid, abs_div, abs_neg, abs_of_pos (by positivity :
      0 < ((m + ς) * ((m + ς) ^ 2 + W0)) * ((m - ς) * ((m - ς) ^ 2 + W0)))]
    have hd : m ^ 6 / 4096 ≤ ((m + ς) * ((m + ς) ^ 2 + W0)) * ((m - ς) * ((m - ς) ^ 2 + W0)) := by
      have h1 : (m / 4) ^ 3 ≤ (m + ς) * ((m + ς) ^ 2 + W0) := by
        have : (m / 4) ^ 3 ≤ (m + ς) ^ 3 := pow_le_pow_left₀ (by positivity) hu0 3
        nlinarith only [this, hW0, hu0p]
      have h2 : (m / 4) ^ 3 ≤ (m - ς) * ((m - ς) ^ 2 + W0) := by
        have : (m / 4) ^ 3 ≤ (m - ς) ^ 3 := pow_le_pow_left₀ (by positivity) hv0 3
        nlinarith only [this, hW0, hv0p]
      have := mul_le_mul h1 h2 (by positivity) (by positivity)
      nlinarith only [this]
    have hnum : |2 * ς * (((m + ς) ^ 2 + (m + ς) * (m - ς) + (m - ς) ^ 2) + W0)| ≤ 6 * (4 + c0) * m ^ 2 := by
      have hs2 : ς ^ 2 ≤ 1 := by nlinarith only [hς'.1, hς'.2]
      have hm2 : (1:ℝ) ≤ m ^ 2 := by nlinarith only [hm]
      have hpos : 0 ≤ ((m + ς) ^ 2 + (m + ς) * (m - ς) + (m - ς) ^ 2) + W0 := by positivity
      rw [abs_mul, abs_of_nonneg hpos, abs_mul, abs_two]
      have hW0c : W0 ≤ c0 * m ^ 2 := by nlinarith only [hW0b, hWbc, hm2, hc0]
      have hbr : ((m + ς) ^ 2 + (m + ς) * (m - ς) + (m - ς) ^ 2) + W0 ≤ (4 + c0) * m ^ 2 := by
        nlinarith only [hs2, hm2, hW0c]
      calc 2 * |ς| * _ ≤ 2 * (3 / 4) * ((4 + c0) * m ^ 2) :=
            mul_le_mul (by linarith) hbr hpos (by norm_num)
        _ ≤ 6 * (4 + c0) * m ^ 2 := by nlinarith only [hc0, hm2]
    calc _ ≤ 6 * (4 + c0) * m ^ 2 / (m ^ 6 / 4096) :=
          div_le_div₀ (by positivity) hnum (by positivity) hd
      _ ≤ 24576 * (4 + c0) / m ^ 4 := by
          apply le_of_eq; field_simp; ring
  have hmain : |M1 + M2| ≤ K * (768 + 24576 * (4 + c0)) * Wb / (n * m ^ 2) := by
    have hid : M1 + M2 = W0 * b * m * (1 / ((m + ς) ^ 2 + W0) - 1 / ((m - ς) ^ 2 + W0)) -
        k * m ^ 2 * W0 * (1 / ((m + ς) * ((m + ς) ^ 2 + W0)) - 1 / ((m - ς) * ((m - ς) ^ 2 + W0))) := by
      rw [hM1, hM2]; ring
    rw [hid]
    have t1 : |W0 * b * m * (1 / ((m + ς) ^ 2 + W0) - 1 / ((m - ς) ^ 2 + W0))| ≤ K * 768 * Wb / (n * m ^ 2) := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hW0, abs_of_pos hm0]
      calc W0 * |b| * m * _ ≤ Wb * (K / n) * m * (768 / m ^ 3) := by gcongr
        _ = K * 768 * Wb / (n * m ^ 2) := by field_simp
    have t2 : |k * m ^ 2 * W0 * (1 / ((m + ς) * ((m + ς) ^ 2 + W0)) - 1 / ((m - ς) * ((m - ς) ^ 2 + W0)))| ≤
        K * (24576 * (4 + c0)) * Wb / (n * m ^ 2) := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hW0, abs_of_nonneg (by positivity : 0 ≤ m ^ 2)]
      calc |k| * m ^ 2 * W0 * _ ≤ (K / n) * m ^ 2 * Wb * (24576 * (4 + c0) / m ^ 4) := by gcongr
        _ = K * (24576 * (4 + c0)) * Wb / (n * m ^ 2) := by field_simp
    calc _ ≤ _ := abs_sub _ _
      _ ≤ K * 768 * Wb / (n * m ^ 2) + K * (24576 * (4 + c0)) * Wb / (n * m ^ 2) := add_le_add t1 t2
      _ = _ := by ring
  have hsplit : (Real.log (1 + W1 / u1 ^ 2) + Real.log (1 + W2 / u2 ^ 2)) -
      (Real.log (1 + W0 / (m + ς) ^ 2) + Real.log (1 + W0 / (m - ς) ^ 2)) =
      (Real.log (1 + W1 / u1 ^ 2) - Real.log (1 + W0 / (m + ς) ^ 2) - M1) +
      (Real.log (1 + W2 / u2 ^ 2) - Real.log (1 + W0 / (m - ς) ^ 2) - M2) + (M1 + M2) := by ring
  rw [hsplit]
  calc _ ≤ |(Real.log (1 + W1 / u1 ^ 2) - Real.log (1 + W0 / (m + ς) ^ 2) - M1) +
      (Real.log (1 + W2 / u2 ^ 2) - Real.log (1 + W0 / (m - ς) ^ 2) - M2)| + |M1 + M2| := abs_add_le _ _
    _ ≤ (CL * Wb / n ^ 2 + CL * Wb / n ^ 2) + K * (768 + 24576 * (4 + c0)) * Wb / (n * m ^ 2) :=
        add_le_add ((abs_add_le _ _).trans (add_le_add A1 A2)) hmain
    _ ≤ _ := by
        have h1 : 0 ≤ 2 * CL * Wb / (n * m ^ 2) := by positivity
        have h2 : 0 ≤ K * (768 + 24576 * (4 + c0)) * Wb / n ^ 2 := by positivity
        have e1 : (2 * CL + K * (768 + 24576 * (4 + c0))) * Wb * (1 / (n * m ^ 2) + 1 / n ^ 2) =
          2 * CL * Wb / (n * m ^ 2) + K * (768 + 24576 * (4 + c0)) * Wb / n ^ 2 +
            (CL * Wb / n ^ 2 + CL * Wb / n ^ 2 + K * (768 + 24576 * (4 + c0)) * Wb / (n * m ^ 2)) := by
          field_simp; ring
        rw [e1]; linarith

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.pair_cancel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pair_cancel

end FormalResearch.ModularBootstrap.FiveTerm
