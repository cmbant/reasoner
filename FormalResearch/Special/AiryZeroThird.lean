module

public import FormalResearch.Special.AiryZeroThirdPhase
public import FormalResearch.Special.AiryZeroThirdLimits

/-!
# DLMF 9.9.18 to relative order `t^{-6}`: the zeros of `Ai` with the `-(5/36) t^{-4}` term

With `t_n = (3π/2)(n - 1/4)` (`airyZeroT`), this module proves for `n ≥ 2`

`|a_n + t^{2/3} (1 + 5/(48 t²) - 5/(36 t⁴))| ≤ 32 t^{-16/3}`      (**`airyZero_third_order`**)

i.e. DLMF 9.9.18 `a_n = -T(t_n)`, `T(t) = t^{2/3}(1 + 5/(48t²) - 5/(36t⁴) + O(t^{-6}))`, with an explicit constant (the true
value of `t^{16/3} |a_n + T₃(t_n)|` increases from `0.481` (`n = 1`) to `77125/82944 = 0.9298` (the next DLMF coefficient; mpmath, 40 digits, `n ≤ 1000`), so the constant is `~34` times
the truth).

**Route.**  `airyZero_phase_third` (`AiryZeroThirdPhase`, from the `u₄`-corrected expansion `AiryZeroThirdChi`, from the
saddle expansion `AiryZeroThirdSaddle`) gives, with `s = r³ = (-a_n)^{3/2}`, `t = g³`:
`s - 5/(32 s) + (1105/6144)/s³ = t + O(s^{-5})`.  Writing `F(x) = x - 5/(32x) + (1105/6144)/x³`, the identity
`F(x) - F(y) = (x - y)(1 + 5/(32xy) - B(x² + xy + y²)/(x³y³))` shows that `F` expands distances by `≥ 0.99` on `[7.9, ∞)`;
the explicit candidate `ŝ = t + 5/(32t) - (1255/6144)/t³` has `|F(ŝ) - t| ≤ (1/8) t^{-5}` (a polynomial identity in `u = t^{-2}`),
hence `|s - ŝ| ≲ 31 t^{-5}`.  The cube `ĝ³` of `ĝ = g (1 + (5/96) u - (145/2048) u²)` differs from `ŝ` by `O(t^{-5})`, and
`airyMin_lemma` (`|a² - b²| min(a,b) ≤ |a³ - b³|`) passes to squares: `|r² - ĝ²| ≤ 32 g^{-16}`; finally `ĝ²` equals
`g²(1 + (5/48)u - (5/36)u²)` up to `g² u³`-terms.

* `airyT3_F_sub`, `airyT3_Fhat`, `airyT3_cube`: the three estimates above;
* **`airyT3_invert`**: `|r² - g² - 5/(48 g⁴) + 5/(36 g^{10})| ≤ 32/g^{16}` from the cube-level hypotheses;
* **`airyZero_third_order`**: the statement above; `airyZero_third_order_exists`: `∃ C ∀ n ≥ 1`;
* **`airyZero_delta_third`**: `|a_n + t^{2/3} + (5/48) t^{-4/3} - (5/36) t^{-10/3}| ≤ 32 t^{-16/3}`;
  `airyZero_delta_tendsto_third`: `t_n^{10/3}(a_n + t^{2/3} + (5/48) t^{-4/3}) → 5/36`.

Proved here: everything stated; no numerics enter the proofs.  **Not formalised:** the coefficient `77125/82944` of `t^{-6}`
(needs `u₅, u₆`-level saddle terms), the zeros of `Ai'` (DLMF 9.9.19).
-/

@[expose] public section

open Set Filter Topology
open scoped Real

namespace FormalResearch.Special

/-- `F(x) = x - 5/(32x) + (1105/6144)/x³`. -/
noncomputable def airyT3F (x : ℝ) : ℝ := x - 5 / (32 * x) + 1105 / (6144 * x ^ 3)

/-- `F` expands distances by at least `99/100` on `[7.9, ∞)`. -/
lemma airyT3_F_sub {x y : ℝ} (hx : 79 / 10 ≤ x) (hy : 79 / 10 ≤ y) :
    |x - y| ≤ 100 / 99 * |airyT3F x - airyT3F y| := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have e : airyT3F x - airyT3F y = (x - y) * (1 + 5 / (32 * x * y) -
      1105 / 6144 * (1 / (x * y ^ 3) + 1 / (x ^ 2 * y ^ 2) + 1 / (x ^ 3 * y))) := by
    unfold airyT3F; field_simp; ring
  have h1 : 1 / (x * y ^ 3) ≤ 1 / (79 / 10) ^ 4 := by
    apply one_div_le_one_div_of_le (by positivity)
    have : (79 / 10 : ℝ) ^ 4 = 79 / 10 * (79 / 10) ^ 3 := by ring
    rw [this]; exact mul_le_mul hx (pow_le_pow_left₀ (by norm_num) hy 3) (by positivity) hx0.le
  have h2 : 1 / (x ^ 2 * y ^ 2) ≤ 1 / (79 / 10) ^ 4 := by
    apply one_div_le_one_div_of_le (by positivity)
    have : (79 / 10 : ℝ) ^ 4 = (79 / 10) ^ 2 * (79 / 10) ^ 2 := by ring
    rw [this]
    exact mul_le_mul (pow_le_pow_left₀ (by norm_num) hx 2) (pow_le_pow_left₀ (by norm_num) hy 2)
      (by positivity) (by positivity)
  have h3 : 1 / (x ^ 3 * y) ≤ 1 / (79 / 10) ^ 4 := by
    apply one_div_le_one_div_of_le (by positivity)
    have : (79 / 10 : ℝ) ^ 4 = (79 / 10) ^ 3 * (79 / 10) := by ring
    rw [this]; exact mul_le_mul (pow_le_pow_left₀ (by norm_num) hx 3) hy (by positivity) (by positivity)
  have h4 : 0 < 5 / (32 * x * y) := by positivity
  have hM : 99 / 100 ≤ 1 + 5 / (32 * x * y) - 1105 / 6144 * (1 / (x * y ^ 3) + 1 / (x ^ 2 * y ^ 2) + 1 / (x ^ 3 * y)) := by
    have : 1105 / 6144 * (1 / (x * y ^ 3) + 1 / (x ^ 2 * y ^ 2) + 1 / (x ^ 3 * y)) ≤ 1105 / 6144 * (3 / (79 / 10) ^ 4) := by
      gcongr; linarith
    have h5 : (1105 / 6144 : ℝ) * (3 / (79 / 10) ^ 4) ≤ 1 / 100 := by norm_num
    linarith
  rw [e, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 1 + 5 / (32 * x * y) -
    1105 / 6144 * (1 / (x * y ^ 3) + 1 / (x ^ 2 * y ^ 2) + 1 / (x ^ 3 * y)))]
  have := mul_le_mul_of_nonneg_left hM (abs_nonneg (x - y))
  nlinarith [abs_nonneg (x - y)]

/-- `|a_0 + a_1 u + … + a_5 u⁵| ≤ 1/8` for the polynomial `N₂(u)` and `0 ≤ u ≤ 1/62`. -/
lemma airyT3_N2_le {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 1 / 62) :
    |2480703750625 / 1424967069597696 * u ^ 5 - 9883281875 / 1855425871872 * u ^ 4 -
      1504148875 / 77309411328 * u ^ 3 + 1851125 / 37748736 * u ^ 2 + 1143275 / 12582912 * u -
      1475 / 12288| ≤ 1 / 8 := by
  have h2 : u ^ 2 ≤ 1 / 62 ^ 2 := by nlinarith
  have h3 : u ^ 3 ≤ 1 / 62 ^ 3 := by
    have := pow_le_pow_left₀ hu0 hu 3; simpa [div_pow] using this
  have h4 : u ^ 4 ≤ 1 / 62 ^ 4 := by
    have := pow_le_pow_left₀ hu0 hu 4; simpa [div_pow] using this
  have h5 : u ^ 5 ≤ 1 / 62 ^ 5 := by
    have := pow_le_pow_left₀ hu0 hu 5; simpa [div_pow] using this
  have p2 : 0 ≤ u ^ 2 := by positivity
  have p3 : 0 ≤ u ^ 3 := by positivity
  have p4 : 0 ≤ u ^ 4 := by positivity
  have p5 : 0 ≤ u ^ 5 := by positivity
  rw [abs_le]; constructor <;> norm_num at h2 h3 h4 h5 ⊢ <;> linarith

lemma airyT3_Fhat_aux {t W : ℝ} (ht : t ≠ 0) (hW : W ≠ 0) :
    (airyT3F (t * W) - t) * (t ^ 5 * W ^ 3) =
      t ^ 6 * W ^ 4 - 5 / 32 * t ^ 4 * W ^ 2 + 1105 / 6144 * t ^ 2 - t ^ 6 * W ^ 3 := by
  unfold airyT3F; field_simp

/-- **The explicit candidate** `ŝ = t + 5/(32 t) - (1255/6144)/t³` satisfies `|F(ŝ) - t| ≤ (1/8) t^{-5}` for `t ≥ 7.9`. -/
lemma airyT3_Fhat {t : ℝ} (ht : 79 / 10 ≤ t) :
    |airyT3F (t + 5 / (32 * t) - 1255 / (6144 * t ^ 3)) - t| ≤ 1 / 8 * (1 / t ^ 5) := by
  have ht0 : 0 < t := by linarith
  set u : ℝ := 1 / t ^ 2 with hu
  have hu0 : 0 < u := by positivity
  have hu62 : u ≤ 1 / 62 := by
    rw [hu]
    apply one_div_le_one_div_of_le (by norm_num)
    nlinarith
  set W : ℝ := 1 + 5 / 32 * u - 1255 / 6144 * u ^ 2 with hW
  have hW1 : 1 ≤ W := by
    rw [hW]; nlinarith
  have hW0 : 0 < W := by linarith
  have hts : t + 5 / (32 * t) - 1255 / (6144 * t ^ 3) = t * W := by
    rw [hW, hu]; field_simp
  rw [hts]
  have key := airyT3_Fhat_aux ht0.ne' hW0.ne'
  have hpoly : t ^ 6 * W ^ 4 - 5 / 32 * t ^ 4 * W ^ 2 + 1105 / 6144 * t ^ 2 - t ^ 6 * W ^ 3 =
      2480703750625 / 1424967069597696 * u ^ 5 - 9883281875 / 1855425871872 * u ^ 4 -
      1504148875 / 77309411328 * u ^ 3 + 1851125 / 37748736 * u ^ 2 + 1143275 / 12582912 * u -
      1475 / 12288 := by
    have ht2 : t ^ 2 = 1 / u := by rw [hu]; field_simp
    rw [hW, show t ^ 6 = (t ^ 2) ^ 3 by ring, show t ^ 4 = (t ^ 2) ^ 2 by ring, ht2]
    field_simp
    ring
  rw [hpoly] at key
  have hN := airyT3_N2_le hu0.le hu62
  have hpos : 0 < t ^ 5 * W ^ 3 := by positivity
  have e2 : airyT3F (t * W) - t = (2480703750625 / 1424967069597696 * u ^ 5 - 9883281875 / 1855425871872 * u ^ 4 -
      1504148875 / 77309411328 * u ^ 3 + 1851125 / 37748736 * u ^ 2 + 1143275 / 12582912 * u -
      1475 / 12288) / (t ^ 5 * W ^ 3) := by
    rw [eq_div_iff hpos.ne']; exact key
  rw [e2, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  have hW3 : 1 ≤ W ^ 3 := one_le_pow₀ hW1
  calc _ ≤ 1 / 8 := hN
    _ ≤ 1 / 8 * (1 / t ^ 5) * (t ^ 5 * W ^ 3) := by
        have : 1 / 8 * (1 / t ^ 5) * (t ^ 5 * W ^ 3) = 1 / 8 * W ^ 3 := by field_simp
        rw [this]; nlinarith

/-- The cube of `ĝ = g + (5/96)/g⁵ - (145/2048)/g^{11}` against the candidate `ŝ` (`t = g³ ≥ 7.9`):
`|ĝ³ - ŝ| ≤ (1/45) t^{-5}`. -/
lemma airyT3_cube {g : ℝ} (hg : 79 / 10 ≤ g ^ 3) :
    |(g + 5 / (96 * g ^ 5) - 145 / (2048 * g ^ 11)) ^ 3 -
        (g ^ 3 + 5 / (32 * g ^ 3) - 1255 / (6144 * (g ^ 3) ^ 3))| ≤ 1 / 45 * (1 / (g ^ 3) ^ 5) := by
  have hg0 : 0 < g := by
    by_contra h; push Not at h
    have : g ^ 3 ≤ 0 := by nlinarith [sq_nonneg g]
    linarith
  set u : ℝ := 1 / g ^ 6 with hu
  have hu0 : 0 < u := by positivity
  have hu62 : u ≤ 1 / 62 := by
    rw [hu]
    apply one_div_le_one_div_of_le (by norm_num)
    nlinarith
  have e : (g + 5 / (96 * g ^ 5) - 145 / (2048 * g ^ 11)) ^ 3 -
      (g ^ 3 + 5 / (32 * g ^ 3) - 1255 / (6144 * (g ^ 3) ^ 3)) =
      g ^ 3 * (-3048625 / 8589934592 * u ^ 6 + 105125 / 134217728 * u ^ 5 + 181975 / 12582912 * u ^ 4 -
        9725 / 442368 * u ^ 3) := by
    rw [hu]; field_simp; ring
  rw [e, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < g ^ 3)]
  have h3 : u ^ 3 = 1 / (g ^ 3) ^ 6 := by rw [hu]; field_simp
  have hp : |-3048625 / 8589934592 * u ^ 6 + 105125 / 134217728 * u ^ 5 + 181975 / 12582912 * u ^ 4 -
      9725 / 442368 * u ^ 3| ≤ 1 / 45 * u ^ 3 := by
    have h4 : u ^ 4 ≤ 1 / 62 * u ^ 3 := by nlinarith [pow_pos hu0 3]
    have h5 : u ^ 5 ≤ 1 / 62 ^ 2 * u ^ 3 := by nlinarith [pow_pos hu0 3, pow_pos hu0 4]
    have h6 : u ^ 6 ≤ 1 / 62 ^ 3 * u ^ 3 := by nlinarith [pow_pos hu0 3, pow_pos hu0 4, pow_pos hu0 5]
    have p3 := pow_pos hu0 3
    have p4 := pow_pos hu0 4
    have p5 := pow_pos hu0 5
    have p6 := pow_pos hu0 6
    rw [abs_le]; constructor <;> norm_num at h5 h6 ⊢ <;> nlinarith
  calc g ^ 3 * |_| ≤ g ^ 3 * (1 / 45 * u ^ 3) := by gcongr
    _ = 1 / 45 * (1 / (g ^ 3) ^ 5) := by
        rw [h3]; field_simp

/-- `ĝ² = g²(1 + (5/48) u - (5/36) u²) + g²(…u³)` for `ĝ = g + (5/96)/g⁵ - (145/2048)/g^{11}`, `u = g^{-6}`. -/
lemma airyT3_sq_hat {g : ℝ} (hg : 0 < g) (hg6 : 62 < g ^ 6) :
    |(g + 5 / (96 * g ^ 5) - 145 / (2048 * g ^ 11)) ^ 2 - g ^ 2 - 5 / (48 * g ^ 4) + 5 / (36 * g ^ 10)| ≤
      1 / 100 * (1 / g ^ 16) := by
  obtain ⟨u, hudef⟩ : ∃ u : ℝ, u = 1 / g ^ 6 := ⟨_, rfl⟩
  have hu0 : 0 < u := by rw [hudef]; positivity
  have hu : u ≤ 1 / 62 := by rw [hudef]; exact one_div_le_one_div_of_le (by norm_num) hg6.le
  have e : (g + 5 / (96 * g ^ 5) - 145 / (2048 * g ^ 11)) ^ 2 - g ^ 2 - 5 / (48 * g ^ 4) + 5 / (36 * g ^ 10) =
      g ^ 2 * (-725 / 98304 * u ^ 3 + 21025 / 4194304 * u ^ 4) := by
    rw [hudef]; field_simp; ring
  rw [e, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < g ^ 2)]
  have h3 : u ^ 3 = 1 / g ^ 18 := by rw [hudef]; field_simp
  have h4 : u ^ 4 ≤ 1 / 62 * u ^ 3 := by nlinarith [pow_pos hu0 3]
  have hp : |-725 / 98304 * u ^ 3 + 21025 / 4194304 * u ^ 4| ≤ 1 / 100 * u ^ 3 := by
    have p3 := pow_pos hu0 3
    have p4 := pow_pos hu0 4
    rw [abs_le]; constructor <;> norm_num at h4 ⊢ <;> nlinarith
  calc g ^ 2 * |_| ≤ g ^ 2 * (1 / 100 * u ^ 3) := by gcongr
    _ = 1 / 100 * (1 / g ^ 16) := by rw [h3]; field_simp

/-- **Inversion to third order.**  For `r > 2`, `g > 0`, with `s = r³`, `t = g³`:
`|s - t - 5/(32 s) + (1105/6144)/s³| ≤ (57/2) s^{-5}` and `|s - t| ≤ (3/5)/s` give
`|r² - g² - 5/(48 g⁴) + 5/(36 g^{10})| ≤ 32/g^{16}`. -/
theorem airyT3_invert {r g : ℝ} (hr : 2 < r) (hg : 0 < g)
    (H1 : |r ^ 3 - g ^ 3 - 5 / (32 * r ^ 3) + 1105 / (6144 * (r ^ 3) ^ 3)| ≤ 57 / 2 * (1 / (r ^ 3) ^ 5))
    (H2 : |r ^ 3 - g ^ 3| ≤ 3 / 5 / r ^ 3) :
    |r ^ 2 - g ^ 2 - 5 / (48 * g ^ 4) + 5 / (36 * g ^ 10)| ≤ 32 / g ^ 16 := by
  have hr0 : 0 < r := by linarith
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = r ^ 3 := ⟨_, rfl⟩
  obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = g ^ 3 := ⟨_, rfl⟩
  have hs8 : 8 < s := by
    rw [hsdef]; nlinarith [pow_lt_pow_left₀ hr (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : 3 ≠ 0)]
  have hs0 : 0 < s := by linarith
  have ht0 : 0 < t := by rw [htdef]; positivity
  rw [← hsdef, ← htdef] at H1 H2
  have hH2 : |s - t| ≤ 3 / 40 := by
    refine H2.trans ?_
    rw [div_le_div_iff₀ hs0 (by norm_num)]; nlinarith
  obtain ⟨hH2a, hH2b⟩ := abs_le.mp hH2
  have ht79 : 79 / 10 ≤ t := by linarith
  have hst : 99 / 100 * t ≤ s := by linarith
  -- Step 1
  have S1 : |airyT3F s - t| ≤ 30 * (1 / t ^ 5) := by
    have e : airyT3F s - t = s - t - 5 / (32 * s) + 1105 / (6144 * s ^ 3) := by unfold airyT3F; ring
    rw [e]
    refine H1.trans ?_
    have h5 : (99 / 100 * t) ^ 5 ≤ s ^ 5 := pow_le_pow_left₀ (by positivity) hst 5
    have : 1 / s ^ 5 ≤ 1 / (99 / 100 * t) ^ 5 := one_div_le_one_div_of_le (by positivity) h5
    calc 57 / 2 * (1 / s ^ 5) ≤ 57 / 2 * (1 / (99 / 100 * t) ^ 5) := by gcongr
      _ = (57 / 2 * (100 / 99) ^ 5) * (1 / t ^ 5) := by field_simp
      _ ≤ 30 * (1 / t ^ 5) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity); norm_num
  -- Step 2
  have S2 := airyT3_Fhat ht79
  set ŝ : ℝ := t + 5 / (32 * t) - 1255 / (6144 * t ^ 3) with hŝ
  have hŝt : t ≤ ŝ := by
    rw [hŝ]
    have ht2 : (1255 / 6144 : ℝ) / t ^ 3 ≤ 5 / 32 / t := by
      rw [div_le_div_iff₀ (by positivity) ht0]; nlinarith [pow_pos ht0 3, mul_pos ht0 ht0]
    have e1 : 1255 / (6144 * t ^ 3) = 1255 / 6144 / t ^ 3 := by field_simp
    have e2 : 5 / (32 * t) = 5 / 32 / t := by field_simp
    rw [e1, e2]; linarith
  -- Step 3
  have S3 : |s - ŝ| ≤ 61 / 2 * (1 / t ^ 5) := by
    have h := airyT3_F_sub (by linarith : 79 / 10 ≤ s) (by linarith : 79 / 10 ≤ ŝ)
    have h' : |airyT3F s - airyT3F ŝ| ≤ (30 + 1 / 8) * (1 / t ^ 5) := by
      have := abs_sub (airyT3F s - t) (airyT3F ŝ - t)
      have e : airyT3F s - airyT3F ŝ = (airyT3F s - t) - (airyT3F ŝ - t) := by ring
      rw [e]
      refine (abs_sub _ _).trans ?_
      linarith
    have hp : 0 < 1 / t ^ 5 := by positivity
    calc |s - ŝ| ≤ 100 / 99 * |airyT3F s - airyT3F ŝ| := h
      _ ≤ 100 / 99 * ((30 + 1 / 8) * (1 / t ^ 5)) := by gcongr
      _ ≤ 61 / 2 * (1 / t ^ 5) := by nlinarith
  -- Step 4: the cube of ĝ
  set ĝ : ℝ := g + 5 / (96 * g ^ 5) - 145 / (2048 * g ^ 11) with hĝ
  have hcube := airyT3_cube (g := g) (by rw [← htdef]; exact ht79)
  rw [← htdef] at hcube
  have S4 : |s - ĝ ^ 3| ≤ 31 * (1 / t ^ 5) := by
    have e : s - ĝ ^ 3 = (s - ŝ) + (ŝ - ĝ ^ 3) := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    have hc : |ŝ - ĝ ^ 3| ≤ 1 / 45 * (1 / t ^ 5) := by
      rw [abs_sub_comm]; exact hcube
    have hp : 0 < 1 / t ^ 5 := by positivity
    linarith
  -- Step 5: from cubes to squares
  have hg6 : 62 < g ^ 6 := by
    have : t ^ 2 = g ^ 6 := by rw [htdef]; ring
    nlinarith
  have hĝg : g ≤ ĝ := by
    rw [hĝ]
    have : (145 / 2048 : ℝ) / g ^ 11 ≤ 5 / 96 / g ^ 5 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have h11 : g ^ 11 = g ^ 5 * g ^ 6 := by ring
      rw [h11]; nlinarith [pow_pos hg 5, mul_pos (pow_pos hg 5) (pow_pos hg 5)]
    have e1 : 145 / (2048 * g ^ 11) = 145 / 2048 / g ^ 11 := by field_simp
    have e2 : 5 / (96 * g ^ 5) = 5 / 96 / g ^ 5 := by field_simp
    rw [e1, e2]; linarith
  have hrg : 99 / 100 * g ≤ r := by
    refine le_of_pow_le_pow_left₀ (by norm_num : 3 ≠ 0) hr0.le ?_
    rw [mul_pow, ← hsdef]
    have : (99 / 100 : ℝ) ^ 3 * g ^ 3 ≤ 99 / 100 * t := by rw [← htdef]; nlinarith [ht0]
    linarith
  have hĝ0 : 0 < ĝ := by linarith
  have hM := airyMin_lemma hr0 hĝ0
  have hmin : 99 / 100 * g ≤ min r ĝ := le_min hrg (by linarith)
  have e15 : 1 / t ^ 5 = 1 / g ^ 15 := by rw [htdef]; ring_nf
  have S5 : |r ^ 2 - ĝ ^ 2| ≤ 157 / 5 * (1 / g ^ 16) := by
    have h1 : |r ^ 2 - ĝ ^ 2| * (99 / 100 * g) ≤ 31 * (1 / g ^ 15) := by
      calc _ ≤ |r ^ 2 - ĝ ^ 2| * min r ĝ := mul_le_mul_of_nonneg_left hmin (abs_nonneg _)
        _ ≤ |r ^ 3 - ĝ ^ 3| := hM
        _ ≤ 31 * (1 / t ^ 5) := by rw [← hsdef]; exact S4
        _ = _ := by rw [e15]
    have hg15 : 0 < g ^ 15 := by positivity
    have hg16 : 0 < g ^ 16 := by positivity
    have h2 : |r ^ 2 - ĝ ^ 2| * (99 / 100 * g ^ 16) ≤ 31 := by
      have := mul_le_mul_of_nonneg_right h1 hg15.le
      rw [mul_assoc, show 31 * (1 / g ^ 15) * g ^ 15 = 31 by field_simp,
        show 99 / 100 * g * g ^ 15 = 99 / 100 * g ^ 16 by ring] at this
      exact this
    have e : 157 / 5 * (1 / g ^ 16) * (99 / 100 * g ^ 16) = 157 * 99 / 500 := by field_simp; norm_num
    have h3 : 157 * 99 / 500 ≥ (31 : ℝ) := by norm_num
    by_contra hcon
    push Not at hcon
    have := mul_lt_mul_of_pos_right hcon (by positivity : 0 < 99 / 100 * g ^ 16)
    rw [e] at this
    linarith
  have S6 := airyT3_sq_hat hg hg6
  rw [← hĝ] at S6
  have hfin : r ^ 2 - g ^ 2 - 5 / (48 * g ^ 4) + 5 / (36 * g ^ 10) =
      (r ^ 2 - ĝ ^ 2) + (ĝ ^ 2 - g ^ 2 - 5 / (48 * g ^ 4) + 5 / (36 * g ^ 10)) := by ring
  rw [hfin]
  refine (abs_add_le _ _).trans ?_
  have : 32 / g ^ 16 = 32 * (1 / g ^ 16) := by ring
  rw [this]
  have hp : 0 < 1 / g ^ 16 := by positivity
  linarith

/-- **DLMF 9.9.18 to relative order `t^{-6}`, explicit constant.**  For `n ≥ 2` and `t = (3π/2)(n - 1/4)`,
`|a_n + t^{2/3} (1 + 5/(48 t²) - 5/(36 t⁴))| ≤ 32 t^{-16/3}`. -/
theorem airyZero_third_order {n : ℕ} (hn : 2 ≤ n) :
    |airyZero n + airyZeroT n ^ (2 / 3 : ℝ) * (1 + 5 / (48 * airyZeroT n ^ 2) - 5 / (36 * airyZeroT n ^ 4))| ≤
      32 * airyZeroT n ^ (-(16 / 3) : ℝ) := by
  have ht0 := airyZeroT_pos (by omega : 1 ≤ n)
  obtain ⟨hw3, hw2, -, -⟩ := airySO_rpow ht0
  set t := airyZeroT n with htdef
  set g := t ^ (1 / 3 : ℝ) with hgdef
  have hg0 : 0 < g := Real.rpow_pos_of_pos ht0 _
  set r := airyZeroRoot n with hr
  have hr2 : 2 < r := two_lt_airyZeroRoot hn
  have hr0 : 0 < r := by linarith
  have hp3 := airyZero_phase_third hn
  have hp0 := airyZero_phase_r hn
  rw [← hr] at hp3 hp0
  have ht : t = 3 * π / 2 * ((n : ℝ) - 1 / 4) := rfl
  have H1 : |r ^ 3 - g ^ 3 - 5 / (32 * r ^ 3) + 1105 / (6144 * (r ^ 3) ^ 3)| ≤ 57 / 2 * (1 / (r ^ 3) ^ 5) := by
    have e : r ^ 3 - g ^ 3 - 5 / (32 * r ^ 3) + 1105 / (6144 * (r ^ 3) ^ 3) =
        3 / 2 * (2 / 3 * r ^ 3 - ((n : ℝ) - 1 / 4) * π - 5 / (48 * r ^ 3) + 1105 / (9216 * r ^ 9)) := by
      rw [hw3, ht]; field_simp; ring
    rw [e, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]
    have e15 : (r ^ 3) ^ 5 = r ^ 15 := by ring
    rw [e15]
    calc 3 / 2 * |_| ≤ 3 / 2 * (19 * (1 / r ^ 15)) := by gcongr
      _ = _ := by ring
  have H2 : |r ^ 3 - g ^ 3| ≤ 3 / 5 / r ^ 3 := by
    have e : r ^ 3 - g ^ 3 = 3 / 2 * (2 / 3 * r ^ 3 - ((n : ℝ) - 1 / 4) * π) := by
      rw [hw3, ht]; ring
    rw [e, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]
    calc 3 / 2 * |_| ≤ 3 / 2 * (2 / 5 / r ^ 3) := by gcongr
      _ = _ := by ring
  have hI := airyT3_invert hr2 hg0 H1 H2
  have ht2 : t ^ 2 = g ^ 6 := by rw [← hw3]; ring
  have ht4 : t ^ 4 = g ^ 12 := by rw [← hw3]; ring
  have hw16 : t ^ (-(16 / 3) : ℝ) = 1 / g ^ 16 := by
    have key : g ^ 16 = t ^ ((16 : ℝ) / 3) := by
      rw [hgdef, ← Real.rpow_natCast, ← Real.rpow_mul ht0.le]; norm_num
    rw [key, one_div, ← Real.rpow_neg ht0.le]
  rw [hw2, hw16, airyZero_eq_neg_root_sq n, ← hr]
  have e : -r ^ 2 + g ^ 2 * (1 + 5 / (48 * t ^ 2) - 5 / (36 * t ^ 4)) =
      -(r ^ 2 - g ^ 2 - 5 / (48 * g ^ 4) + 5 / (36 * g ^ 10)) := by
    rw [ht2, ht4]; field_simp; ring
  rw [e, abs_neg]
  calc _ ≤ 32 / g ^ 16 := hI
    _ = _ := by ring

/-- `|a_n + t^{2/3} + (5/48) t^{-4/3} - (5/36) t^{-10/3}| ≤ 32 t^{-16/3}` for `n ≥ 2`. -/
theorem airyZero_delta_third {n : ℕ} (hn : 2 ≤ n) :
    |airyZero n + airyZeroT n ^ (2 / 3 : ℝ) + 5 / 48 * airyZeroT n ^ (-(4 / 3) : ℝ) -
        5 / 36 * airyZeroT n ^ (-(10 / 3) : ℝ)| ≤ 32 * airyZeroT n ^ (-(16 / 3) : ℝ) := by
  have ht0 := airyZeroT_pos (by omega : 1 ≤ n)
  obtain ⟨hw3, hw2, hw4, hw10⟩ := airySO_rpow ht0
  have h := airyZero_third_order hn
  set t := airyZeroT n
  set g := t ^ (1 / 3 : ℝ)
  have hg0 : 0 < g := Real.rpow_pos_of_pos ht0 _
  have ht2 : t ^ 2 = g ^ 6 := by rw [← hw3]; ring
  have ht4 : t ^ 4 = g ^ 12 := by rw [← hw3]; ring
  have e : airyZero n + t ^ (2 / 3 : ℝ) + 5 / 48 * t ^ (-(4 / 3) : ℝ) - 5 / 36 * t ^ (-(10 / 3) : ℝ) =
      airyZero n + t ^ (2 / 3 : ℝ) * (1 + 5 / (48 * t ^ 2) - 5 / (36 * t ^ 4)) := by
    rw [hw2, hw4, hw10, ht2, ht4]; field_simp; ring
  rw [e]; exact h

/-- **Third order, all `n ≥ 1`**: `∃ C ∀ n ≥ 1, |a_n + t_n^{2/3}(1 + 5/(48 t_n²) - 5/(36 t_n⁴))| ≤ C t_n^{-16/3}`. -/
theorem airyZero_third_order_exists :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      |airyZero n + airyZeroT n ^ (2 / 3 : ℝ) * (1 + 5 / (48 * airyZeroT n ^ 2) - 5 / (36 * airyZeroT n ^ 4))| ≤
        C * airyZeroT n ^ (-(16 / 3) : ℝ) := by
  refine ⟨max 32 (|airyZero 1 + airyZeroT 1 ^ (2 / 3 : ℝ) *
    (1 + 5 / (48 * airyZeroT 1 ^ 2) - 5 / (36 * airyZeroT 1 ^ 4))| / airyZeroT 1 ^ (-(16 / 3) : ℝ)),
    fun n hn => ?_⟩
  rcases hn.eq_or_lt with rfl | h2
  · have hp : 0 < airyZeroT 1 ^ (-(16 / 3) : ℝ) := Real.rpow_pos_of_pos (airyZeroT_pos le_rfl) _
    rw [← div_le_iff₀ hp]
    exact le_max_right _ _
  · have hp : 0 < airyZeroT n ^ (-(16 / 3) : ℝ) := Real.rpow_pos_of_pos (airyZeroT_pos (by omega)) _
    refine (airyZero_third_order h2).trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hp.le

/-- **The next coefficient as a limit**: `t_n^{10/3}(a_n + t_n^{2/3} + (5/48) t_n^{-4/3}) → 5/36`. -/
theorem airyZero_delta_tendsto_third :
    Tendsto (fun n : ℕ => airyZeroT n ^ (10 / 3 : ℝ) *
      (airyZero n + airyZeroT n ^ (2 / 3 : ℝ) + 5 / 48 * airyZeroT n ^ (-(4 / 3) : ℝ))) atTop (𝓝 (5 / 36)) := by
  have hz : Tendsto (fun n : ℕ => 32 * ((n : ℝ) ^ 2)⁻¹) atTop (𝓝 0) := by
    have := (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (α := ℝ) (n := 2) two_ne_zero
      |>.comp tendsto_natCast_atTop_atTop)).const_mul 32
    simpa using this
  have hY : Tendsto (fun n : ℕ => airyZeroT n ^ (10 / 3 : ℝ) *
      (airyZero n + airyZeroT n ^ (2 / 3 : ℝ) + 5 / 48 * airyZeroT n ^ (-(4 / 3) : ℝ) -
        5 / 36 * airyZeroT n ^ (-(10 / 3) : ℝ))) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hz
    filter_upwards [eventually_ge_atTop 2] with n hn
    have ht0 := airyZeroT_pos (by omega : 1 ≤ n)
    have hge : (n : ℝ) ≤ airyZeroT n := airyZeroT_ge (by omega)
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have h := airyZero_delta_third hn
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht0 _)]
    calc airyZeroT n ^ (10 / 3 : ℝ) * |_| ≤ airyZeroT n ^ (10 / 3 : ℝ) * (32 * airyZeroT n ^ (-(16 / 3) : ℝ)) := by
          gcongr
      _ = 32 * (airyZeroT n ^ 2)⁻¹ := by
          rw [← mul_assoc, mul_comm _ (32 : ℝ), mul_assoc, ← Real.rpow_add ht0]
          have : (10 / 3 : ℝ) + -(16 / 3) = -(2 : ℝ) := by norm_num
          rw [this, Real.rpow_neg ht0.le]; norm_cast
      _ ≤ 32 * ((n : ℝ) ^ 2)⁻¹ := by
          gcongr
  have h2 := hY.add_const (5 / 36)
  rw [zero_add] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have ht0 := airyZeroT_pos hn
  have : airyZeroT n ^ (10 / 3 : ℝ) * airyZeroT n ^ (-(10 / 3) : ℝ) = 1 := by
    rw [← Real.rpow_add ht0]; norm_num
  linear_combination (-(5 / 36)) * this

end FormalResearch.Special

/-- info: 'FormalResearch.Special.airyT3_F_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyT3_F_sub

/-- info: 'FormalResearch.Special.airyT3_Fhat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyT3_Fhat

/-- info: 'FormalResearch.Special.airyT3_cube' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyT3_cube

/-- info: 'FormalResearch.Special.airyT3_invert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyT3_invert

/-- info: 'FormalResearch.Special.airyZero_third_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyZero_third_order

/-- info: 'FormalResearch.Special.airyZero_delta_third' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyZero_delta_third

/-- info: 'FormalResearch.Special.airyZero_third_order_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyZero_third_order_exists

/-- info: 'FormalResearch.Special.airyZero_delta_tendsto_third' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyZero_delta_tendsto_third

