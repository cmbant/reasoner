import Mathlib

/-!
# The real inequality of the sharp critical-orbit stability (`CO-2`)

Source: `ResearchNotes/QI/four_qubit_entropy/critical_orbit_stability.tex`, proof of
`thm:fqe-critical-orbit-sharp`, from "Assume henceforth that `Φ(v) ≤ 1/2`" to the decoupled bound
`Q(v) + 2Φ_im(v) - 3/2 ≥ 𝒴(r₀,y) + 𝒳(p;x²) ≥ 0`.

Everything here is a statement about real numbers.  The normalised critical vector is
`v = (r, x₁ + i y₁, x₂ + i y₂, x₃ + i y₃)` with `r > 0`, `y_j ≥ 0`, `N = 1` and `t = √3`; the hypotheses are:

* `hp`: `p_j = x_j² + y_j² ≤ p₀ = r²` (the cut probabilities `|v_j|²` are at most the largest `p₀`);
* `hl`: the eight cut probabilities of the two other cuts, `¼|r + Σ ε_j v_j|² ≤ p₀` for all `ε ∈ {±1}³`;
* `hΦ`: `Φ_im = (r/√2 + S_y/√6)² ≤ 1/2`, written `r²/2 + S_y²/6 + t r S_y/3 ≤ 1/2`.

`core_real` is the three-term form `Q = ½ + 18 ∑_j D_j (c_{0j}² - c_{kl}²)` (`N = 1`) of the sextic `Q`:
`Q + 2Φ_im ≥ 3/2`.  The proof follows the paper: `S_y ≤ √3(1-r)`, `S_x ≤ r`, `|x_j| ≤ (4r²-1)/(2r)`, `r ≥ 3/5`
(`core_constraints`); `Y ≥ 0` by the AM-GM bound (`Y_nonneg`); `X ≥ 0` by the square on `[19/25, 1]` and the concave
polynomials `P₁, P₂` on `[3/5,16/25]`, `[16/25,19/25]` (`X_nonneg`).  No numerics beyond rational polynomial
inequalities in one variable.
-/

namespace FormalResearch.FourQubitEntropy.CO

theorem t_lt {t : ℝ} (ht : t ^ 2 = 3) (ht0 : 0 < t) : t < 26 / 15 := by nlinarith

theorem Sy_le {t r Sy : ℝ} (ht : t ^ 2 = 3) (ht0 : 0 < t) (hr1 : r ≤ 1) (hr0 : 0 < r)
    (hΦ : r ^ 2 / 2 + Sy ^ 2 / 6 + t * r * Sy / 3 ≤ 1 / 2) : Sy ≤ t * (1 - r) := by
  by_contra h
  push Not at h
  have h1 : 0 ≤ 1 - r := by linarith
  nlinarith [mul_pos ht0 hr0, mul_nonneg ht0.le h1, sq_nonneg (Sy - t * (1 - r)),
    mul_pos (sub_pos.2 h) hr0, mul_pos (sub_pos.2 h) ht0]

/-- sign-aligned sums: the key consequences of the eight cut-probability bounds. -/
theorem Sx_le {r x1 x2 x3 y1 y2 y3 : ℝ} (hr : 0 < r)
    (hl : ∀ s1 s2 s3 : ℝ, s1 ^ 2 = 1 → s2 ^ 2 = 1 → s3 ^ 2 = 1 →
      (r + s1 * x1 + s2 * x2 + s3 * x3) ^ 2 + (s1 * y1 + s2 * y2 + s3 * y3) ^ 2 ≤ 4 * r ^ 2) :
    |x1| + |x2| + |x3| ≤ r := by
  have sg : ∀ x : ℝ, ∃ s : ℝ, s ^ 2 = 1 ∧ s * x = |x| := by
    intro x
    by_cases h : 0 ≤ x
    · exact ⟨1, by norm_num, by rw [abs_of_nonneg h]; ring⟩
    · exact ⟨-1, by norm_num, by rw [abs_of_neg (not_le.1 h)]; ring⟩
  obtain ⟨s1, h1, e1⟩ := sg x1
  obtain ⟨s2, h2, e2⟩ := sg x2
  obtain ⟨s3, h3, e3⟩ := sg x3
  have hh := hl s1 s2 s3 h1 h2 h3
  have e : r + s1 * x1 + s2 * x2 + s3 * x3 = r + (|x1| + |x2| + |x3|) := by rw [← e1, ← e2, ← e3]; ring
  rw [e] at hh
  have h' : (r + (|x1| + |x2| + |x3|)) ^ 2 ≤ 4 * r ^ 2 := by
    nlinarith only [hh, sq_nonneg (s1 * y1 + s2 * y2 + s3 * y3)]
  have hS : 0 ≤ |x1| + |x2| + |x3| := by positivity
  nlinarith only [h', hS, hr]


theorem sg_exists (x : ℝ) : ∃ s : ℝ, s ^ 2 = 1 ∧ s * x = |x| := by
  by_cases h : 0 ≤ x
  · exact ⟨1, by norm_num, by rw [abs_of_nonneg h]; ring⟩
  · exact ⟨-1, by norm_num, by rw [abs_of_neg (not_le.1 h)]; ring⟩

/-- Averaging over the four sign vectors with `ε₁ = sgn x₁`: `2 r |x₁| + 1 ≤ 4 r²`. -/
theorem xj_le {r x1 x2 x3 y1 y2 y3 : ℝ}
    (hN : r ^ 2 + (x1 ^ 2 + y1 ^ 2) + (x2 ^ 2 + y2 ^ 2) + (x3 ^ 2 + y3 ^ 2) = 1)
    (hl : ∀ s1 s2 s3 : ℝ, s1 ^ 2 = 1 → s2 ^ 2 = 1 → s3 ^ 2 = 1 →
      (r + s1 * x1 + s2 * x2 + s3 * x3) ^ 2 + (s1 * y1 + s2 * y2 + s3 * y3) ^ 2 ≤ 4 * r ^ 2) :
    2 * r * |x1| + 1 ≤ 4 * r ^ 2 := by
  obtain ⟨s, hs, e⟩ := sg_exists x1
  have i1 := hl s 1 1 hs (by norm_num) (by norm_num)
  have i2 := hl s 1 (-1) hs (by norm_num) (by norm_num)
  have i3 := hl s (-1) 1 hs (by norm_num) (by norm_num)
  have i4 := hl s (-1) (-1) hs (by norm_num) (by norm_num)
  have hy : s ^ 2 * y1 ^ 2 = y1 ^ 2 := by rw [hs]; ring
  have hx : |x1| ^ 2 = x1 ^ 2 := sq_abs x1
  have e2 : (s * x1) ^ 2 = x1 ^ 2 := by rw [e, hx]
  have hrs : r * (s * x1) = r * |x1| := by rw [e]
  nlinarith only [i1, i2, i3, i4, hy, hx, e2, hN, hrs]


/-- `2 s₂ ≤ (2r-1)²` and `q₄ ≤ ¼ (2r-1)⁴` (the `q₄` bound of `CO-2`). -/
theorem q4_bound {r A1 A2 A3 : ℝ} (hr : 3 / 5 ≤ r) (hr1 : r ≤ 1) (h1 : 0 ≤ A1) (h2 : 0 ≤ A2) (h3 : 0 ≤ A3)
    (hSx : A1 + A2 + A3 ≤ r)
    (hS7 : (r + (A1 + A2 + A3)) ^ 2 ≤ (3 * r - 1) ^ 2 + 2 * (A1 ^ 2 + A2 ^ 2 + A3 ^ 2)) :
    A1 ^ 2 * A2 ^ 2 + A1 ^ 2 * A3 ^ 2 + A2 ^ 2 * A3 ^ 2 ≤ (2 * r - 1) ^ 4 / 4 := by
  set Sx := A1 + A2 + A3 with hSxd
  set X2 := A1 ^ 2 + A2 ^ 2 + A3 ^ 2 with hX2d
  have hSx0 : 0 ≤ Sx := by positivity
  have hX20 : 0 ≤ X2 := by positivity
  have hc : 0 < 3 * r - 1 := by linarith only [hr]
  set z := X2 / (3 * r - 1) with hz
  have hz0 : 0 ≤ z := div_nonneg hX20 hc.le
  have hXz : X2 = z * (3 * r - 1) := by rw [hz]; field_simp
  have hSxz : Sx ≤ 2 * r - 1 + z := by
    have h : (r + Sx) ^ 2 ≤ ((3 * r - 1) + z) ^ 2 := by
      rw [hXz] at hS7
      nlinarith only [hS7, sq_nonneg z]
    have hnn : 0 ≤ (3 * r - 1) + z := by positivity
    have := (sq_le_sq₀ (by linarith only [hr, hSx0] : 0 ≤ r + Sx) hnn).1 h
    linarith only [this]
  have hs2 : Sx ^ 2 - X2 ≤ (2 * r - 1) ^ 2 := by
    by_cases hzc : z ≤ 1 - r
    · have hnn : 0 ≤ 2 * r - 1 + z := by linarith only [hr, hz0]
      have h := pow_le_pow_left₀ hSx0 hSxz 2
      rw [hXz] at *
      nlinarith only [h, mul_nonneg hz0 (sub_nonneg.2 hzc)]
    · push Not at hzc
      have h := pow_le_pow_left₀ hSx0 hSx 2
      have : z * (3 * r - 1) ≥ (1 - r) * (3 * r - 1) := mul_le_mul_of_nonneg_right hzc.le hc.le
      rw [hXz]
      nlinarith only [h, this]
  have hs2d : 2 * (A1 * A2 + A1 * A3 + A2 * A3) ≤ (2 * r - 1) ^ 2 := by
    have : Sx ^ 2 - X2 = 2 * (A1 * A2 + A1 * A3 + A2 * A3) := by rw [hSxd, hX2d]; ring
    linarith only [hs2, this]
  have hs0 : 0 ≤ A1 * A2 + A1 * A3 + A2 * A3 := by positivity
  have hq : A1 ^ 2 * A2 ^ 2 + A1 ^ 2 * A3 ^ 2 + A2 ^ 2 * A3 ^ 2 ≤ (A1 * A2 + A1 * A3 + A2 * A3) ^ 2 := by
    nlinarith only [mul_nonneg (mul_nonneg h1 h2) (mul_nonneg h1 h3), mul_nonneg (mul_nonneg h1 h2) (mul_nonneg h2 h3),
      mul_nonneg (mul_nonneg h1 h3) (mul_nonneg h2 h3)]
  have : (A1 * A2 + A1 * A3 + A2 * A3) ^ 2 ≤ ((2 * r - 1) ^ 2 / 2) ^ 2 :=
    pow_le_pow_left₀ hs0 (by linarith only [hs2d]) 2
  nlinarith only [hq, this]


/-- The consequences of the cut-probability bounds used in `CO-2`. -/
theorem core_constraints {t r x1 x2 x3 y1 y2 y3 : ℝ} (ht : t ^ 2 = 3) (ht0 : 0 < t) (hr0 : 0 < r)
    (hy1 : 0 ≤ y1) (hy2 : 0 ≤ y2) (hy3 : 0 ≤ y3)
    (hN : r ^ 2 + (x1 ^ 2 + y1 ^ 2) + (x2 ^ 2 + y2 ^ 2) + (x3 ^ 2 + y3 ^ 2) = 1)
    (hp1 : x1 ^ 2 + y1 ^ 2 ≤ r ^ 2) (hp2 : x2 ^ 2 + y2 ^ 2 ≤ r ^ 2) (hp3 : x3 ^ 2 + y3 ^ 2 ≤ r ^ 2)
    (hl : ∀ s1 s2 s3 : ℝ, s1 ^ 2 = 1 → s2 ^ 2 = 1 → s3 ^ 2 = 1 →
      (r + s1 * x1 + s2 * x2 + s3 * x3) ^ 2 + (s1 * y1 + s2 * y2 + s3 * y3) ^ 2 ≤ 4 * r ^ 2)
    (hΦ : r ^ 2 / 2 + (y1 + y2 + y3) ^ 2 / 6 + t * r * (y1 + y2 + y3) / 3 ≤ 1 / 2) :
    r ≤ 1 ∧ y1 + y2 + y3 ≤ t * (1 - r) ∧ 3 / 5 ≤ r ∧
    1 / 15 * (1 - r) * (15 - 11 * r) ≤ x1 ^ 2 + x2 ^ 2 + x3 ^ 2 ∧
    2 * (1 - r) * (2 * r - 1) ≤ x1 ^ 2 + x2 ^ 2 + x3 ^ 2 ∧
    x1 ^ 2 * x2 ^ 2 + x1 ^ 2 * x3 ^ 2 + x2 ^ 2 * x3 ^ 2 ≤ (2 * r - 1) ^ 4 / 4 := by
  have hr1 : r ≤ 1 := by nlinarith only [hN, sq_nonneg x1, sq_nonneg x2, sq_nonneg x3, sq_nonneg y1, sq_nonneg y2, sq_nonneg y3, hr0]
  have hSy0 : 0 ≤ y1 + y2 + y3 := by positivity
  have hSy := Sy_le ht ht0 hr1 hr0 hΦ
  have hSx := Sx_le hr0 hl
  have hx1 := xj_le hN hl
  have hx2 : 2 * r * |x2| + 1 ≤ 4 * r ^ 2 := by
    refine xj_le (x1 := x2) (x2 := x1) (x3 := x3) (y1 := y2) (y2 := y1) (y3 := y3) (by linarith only [hN]) ?_
    intro s1 s2 s3 h1 h2 h3
    have := hl s2 s1 s3 h2 h1 h3
    linarith only [this]
  have hx3 : 2 * r * |x3| + 1 ≤ 4 * r ^ 2 := by
    refine xj_le (x1 := x3) (x2 := x1) (x3 := x2) (y1 := y3) (y2 := y1) (y3 := y2) (by linarith only [hN]) ?_
    intro s1 s2 s3 h1 h2 h3
    have := hl s2 s3 s1 h2 h3 h1
    linarith only [this]
  -- y_j ≤ r
  have hyr1 : y1 ≤ r := by nlinarith only [hp1, sq_nonneg x1, hy1, hr0]
  have hyr2 : y2 ≤ r := by nlinarith only [hp2, sq_nonneg x2, hy2, hr0]
  have hyr3 : y3 ≤ r := by nlinarith only [hp3, sq_nonneg x3, hy3, hr0]
  have ht2 := t_lt ht ht0
  have hY2a : y1 ^ 2 + y2 ^ 2 + y3 ^ 2 ≤ r * (y1 + y2 + y3) := by
    nlinarith only [mul_le_mul_of_nonneg_right hyr1 hy1, mul_le_mul_of_nonneg_right hyr2 hy2,
      mul_le_mul_of_nonneg_right hyr3 hy3]
  have hY2b : r * (y1 + y2 + y3) ≤ 26 / 15 * r * (1 - r) := by
    have h1 : y1 + y2 + y3 ≤ 26 / 15 * (1 - r) := by
      nlinarith only [hSy, ht2, sub_nonneg.2 hr1]
    nlinarith only [mul_le_mul_of_nonneg_left h1 hr0.le]
  have hSy2 : (y1 + y2 + y3) ^ 2 ≤ 3 * (1 - r) ^ 2 := by
    have h1 : (y1 + y2 + y3) ^ 2 ≤ (t * (1 - r)) ^ 2 := pow_le_pow_left₀ hSy0 hSy 2
    have h2 : (t * (1 - r)) ^ 2 = 3 * (1 - r) ^ 2 := by rw [mul_pow, ht]
    linarith only [h1, h2]
  have hY2c : y1 ^ 2 + y2 ^ 2 + y3 ^ 2 ≤ 3 * (1 - r) ^ 2 := by
    nlinarith only [hSy2, mul_nonneg hy1 hy2, mul_nonneg hy1 hy3, mul_nonneg hy2 hy3]
  have hX2eq : x1 ^ 2 + x2 ^ 2 + x3 ^ 2 = 1 - r ^ 2 - (y1 ^ 2 + y2 ^ 2 + y3 ^ 2) := by linarith only [hN]
  have hL1 : 1 / 15 * (1 - r) * (15 - 11 * r) ≤ x1 ^ 2 + x2 ^ 2 + x3 ^ 2 := by
    rw [hX2eq]; nlinarith only [hY2a, hY2b]
  have hL2 : 2 * (1 - r) * (2 * r - 1) ≤ x1 ^ 2 + x2 ^ 2 + x3 ^ 2 := by
    rw [hX2eq]; nlinarith only [hY2c]
  -- X2 ≤ 2 r² - 1/2
  have hA1 : 2 * r * x1 ^ 2 ≤ (4 * r ^ 2 - 1) * |x1| := by
    have : x1 ^ 2 = |x1| * |x1| := by rw [← sq, sq_abs]
    rw [this]; nlinarith only [mul_le_mul_of_nonneg_right hx1 (abs_nonneg x1)]
  have hA2 : 2 * r * x2 ^ 2 ≤ (4 * r ^ 2 - 1) * |x2| := by
    have : x2 ^ 2 = |x2| * |x2| := by rw [← sq, sq_abs]
    rw [this]; nlinarith only [mul_le_mul_of_nonneg_right hx2 (abs_nonneg x2)]
  have hA3 : 2 * r * x3 ^ 2 ≤ (4 * r ^ 2 - 1) * |x3| := by
    have : x3 ^ 2 = |x3| * |x3| := by rw [← sq, sq_abs]
    rw [this]; nlinarith only [mul_le_mul_of_nonneg_right hx3 (abs_nonneg x3)]
  have h4r : 0 ≤ 4 * r ^ 2 - 1 := by nlinarith only [hx1, mul_nonneg hr0.le (abs_nonneg x1)]
  have hX2le : x1 ^ 2 + x2 ^ 2 + x3 ^ 2 ≤ 2 * r ^ 2 - 1 / 2 := by
    have hsum : 2 * r * (x1 ^ 2 + x2 ^ 2 + x3 ^ 2) ≤ (4 * r ^ 2 - 1) * r := by
      have := mul_le_mul_of_nonneg_left hSx h4r
      nlinarith only [hA1, hA2, hA3, this]
    nlinarith only [hsum, hr0]
  have hr35 : 3 / 5 ≤ r := by
    have h1 : 1 ≤ r ^ 2 + (2 * r ^ 2 - 1 / 2) + 7 / 4 * r * (1 - r) := by
      have hY74 : y1 ^ 2 + y2 ^ 2 + y3 ^ 2 ≤ 7 / 4 * r * (1 - r) := by
        nlinarith only [hY2a, hY2b, mul_nonneg hr0.le (sub_nonneg.2 hr1)]
      nlinarith only [hN, hX2le, hY74]
    nlinarith only [h1, hr0]
  -- S7
  have hsg := sg_exists
  obtain ⟨s1, hs1, e1⟩ := hsg x1
  obtain ⟨s2, hs2, e2⟩ := hsg x2
  obtain ⟨s3, hs3, e3⟩ := hsg x3
  have hh := hl s1 s2 s3 hs1 hs2 hs3
  have e : r + s1 * x1 + s2 * x2 + s3 * x3 = r + (|x1| + |x2| + |x3|) := by rw [← e1, ← e2, ← e3]; ring
  rw [e] at hh
  have hcross : (s1 * y1 + s2 * y2 + s3 * y3) ^ 2 ≥ 2 * (y1 ^ 2 + y2 ^ 2 + y3 ^ 2) - (y1 + y2 + y3) ^ 2 := by
    have a1 : s1 ^ 2 * y1 ^ 2 = y1 ^ 2 := by rw [hs1]; ring
    have a2 : s2 ^ 2 * y2 ^ 2 = y2 ^ 2 := by rw [hs2]; ring
    have a3 : s3 ^ 2 * y3 ^ 2 = y3 ^ 2 := by rw [hs3]; ring
    have b12 : s1 * s2 ≥ -1 := by nlinarith only [sq_nonneg (s1 + s2), hs1, hs2]
    have b13 : s1 * s3 ≥ -1 := by nlinarith only [sq_nonneg (s1 + s3), hs1, hs3]
    have b23 : s2 * s3 ≥ -1 := by nlinarith only [sq_nonneg (s2 + s3), hs2, hs3]
    nlinarith only [a1, a2, a3, mul_nonneg hy1 hy2, mul_nonneg hy1 hy3, mul_nonneg hy2 hy3,
      mul_le_mul_of_nonneg_right b12 (mul_nonneg hy1 hy2), mul_le_mul_of_nonneg_right b13 (mul_nonneg hy1 hy3),
      mul_le_mul_of_nonneg_right b23 (mul_nonneg hy2 hy3)]
  have hS7 : (r + (|x1| + |x2| + |x3|)) ^ 2 ≤ (3 * r - 1) ^ 2 +
      2 * (|x1| ^ 2 + |x2| ^ 2 + |x3| ^ 2) := by
    rw [sq_abs, sq_abs, sq_abs]
    nlinarith only [hh, hcross, hX2eq, hSy2]
  have hq4 := q4_bound hr35 hr1 (abs_nonneg x1) (abs_nonneg x2) (abs_nonneg x3) hSx hS7
  rw [sq_abs, sq_abs, sq_abs] at hq4
  exact ⟨hr1, hSy, hr35, hL1, hL2, hq4⟩



theorem poly_aux {r : ℝ} (hr : 3 / 5 ≤ r) (hr1 : r ≤ 1) : (4 * r ^ 2 - 1) * (1 - r) ^ 2 ≤ 1 / 9 := by
  nlinarith [sq_nonneg (r - 17 / 25), sq_nonneg (r ^ 2 - 17 / 25 * r), mul_nonneg (sub_nonneg.2 hr) (sub_nonneg.2 hr1),
    mul_nonneg (mul_nonneg (sub_nonneg.2 hr) (sub_nonneg.2 hr1)) (sub_nonneg.2 hr1), sq_nonneg (r ^ 2 - 1 / 2)]

theorem sig_le (y1 y2 y3 : ℝ) : y1 * y2 + y1 * y3 + y2 * y3 ≤ (y1 + y2 + y3) ^ 2 / 3 := by
  nlinarith only [sq_nonneg (y1 - y2), sq_nonneg (y1 - y3), sq_nonneg (y2 - y3)]

theorem prod_le {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : a * b ≤ (a + b + c) ^ 2 / 4 := by
  nlinarith only [sq_nonneg (a - b), mul_nonneg hc (add_nonneg ha hb), mul_nonneg hc hc, ha, hb]

theorem Y_nonneg {t r y1 y2 y3 w1 w2 w3 : ℝ} (ht : t ^ 2 = 3) (ht0 : 0 < t) (hr : 3 / 5 ≤ r) (hr1 : r ≤ 1)
    (h1 : 0 ≤ y1) (h2 : 0 ≤ y2) (h3 : 0 ≤ y3) (hSy : y1 + y2 + y3 ≤ t * (1 - r))
    (hw1 : 0 ≤ w1) (hw2 : 0 ≤ w2) (hw3 : 0 ≤ w3)
    (hw1' : w1 ≤ 4 * r ^ 2 - 1) (hw2' : w2 ≤ 4 * r ^ 2 - 1) (hw3' : w3 ≤ 4 * r ^ 2 - 1) :
    0 ≤ 2 / 3 * (t * r * (y1 + y2 + y3) - (y1 ^ 2 + y2 ^ 2 + y3 ^ 2) + (y1 * y2 + y1 * y3 + y2 * y3))
      - 36 * (w1 * (y2 ^ 2 * y3 ^ 2) + w2 * (y1 ^ 2 * y3 ^ 2) + w3 * (y1 ^ 2 * y2 ^ 2)) := by
  have hSy0 : 0 ≤ y1 + y2 + y3 := by positivity
  have hσ0 : 0 ≤ y1 * y2 + y1 * y3 + y2 * y3 := by positivity
  have hp12 := prod_le h1 h2 h3
  have hp13 : y1 * y3 ≤ (y1 + y2 + y3) ^ 2 / 4 := by
    have := prod_le h1 h3 h2; rwa [show y1 + y3 + y2 = y1 + y2 + y3 by ring] at this
  have hp23 : y2 * y3 ≤ (y1 + y2 + y3) ^ 2 / 4 := by
    have := prod_le h2 h3 h1; rwa [show y2 + y3 + y1 = y1 + y2 + y3 by ring] at this
  set Sy := y1 + y2 + y3 with hSydef
  set σ := y1 * y2 + y1 * y3 + y2 * y3 with hσ
  have hY2 : y1 ^ 2 + y2 ^ 2 + y3 ^ 2 = Sy ^ 2 - 2 * σ := by rw [hSydef, hσ]; ring
  have hSy2 : Sy ^ 2 ≤ 3 * (1 - r) ^ 2 := by
    have : Sy ^ 2 ≤ (t * (1 - r)) ^ 2 := pow_le_pow_left₀ hSy0 hSy 2
    calc Sy ^ 2 ≤ (t * (1 - r)) ^ 2 := this
      _ = 3 * (1 - r) ^ 2 := by rw [mul_pow, ht]
  have e1 : y2 ^ 2 * y3 ^ 2 ≤ Sy ^ 2 / 4 * (y2 * y3) := by
    have := mul_le_mul_of_nonneg_left hp23 (mul_nonneg h2 h3)
    nlinarith only [this]
  have e2 : y1 ^ 2 * y3 ^ 2 ≤ Sy ^ 2 / 4 * (y1 * y3) := by
    have := mul_le_mul_of_nonneg_left hp13 (mul_nonneg h1 h3)
    nlinarith only [this]
  have e3 : y1 ^ 2 * y2 ^ 2 ≤ Sy ^ 2 / 4 * (y1 * y2) := by
    have := mul_le_mul_of_nonneg_left hp12 (mul_nonneg h1 h2)
    nlinarith only [this]
  have hq : y2 ^ 2 * y3 ^ 2 + y1 ^ 2 * y3 ^ 2 + y1 ^ 2 * y2 ^ 2 ≤ Sy ^ 2 / 4 * σ := by
    rw [hσ]; nlinarith only [e1, e2, e3]
  have hr2 : 0 ≤ 4 * r ^ 2 - 1 := by nlinarith only [hr]
  have hwq : w1 * (y2 ^ 2 * y3 ^ 2) + w2 * (y1 ^ 2 * y3 ^ 2) + w3 * (y1 ^ 2 * y2 ^ 2) ≤
      (4 * r ^ 2 - 1) * (Sy ^ 2 / 4 * σ) := by
    have a1 := mul_le_mul hw1' (le_refl (y2 ^ 2 * y3 ^ 2)) (by positivity) hr2
    have a2 := mul_le_mul hw2' (le_refl (y1 ^ 2 * y3 ^ 2)) (by positivity) hr2
    have a3 := mul_le_mul hw3' (le_refl (y1 ^ 2 * y2 ^ 2)) (by positivity) hr2
    have a4 := mul_le_mul_of_nonneg_left hq hr2
    nlinarith only [a1, a2, a3, a4]
  have h4 := poly_aux hr hr1
  have hnum : 9 * (4 * r ^ 2 - 1) * Sy ^ 2 ≤ 3 := by
    have h9 := mul_le_mul_of_nonneg_left hSy2 (mul_nonneg (by norm_num : (0:ℝ) ≤ 9) hr2)
    have e : 9 * (4 * r ^ 2 - 1) * (3 * (1 - r) ^ 2) = 27 * ((4 * r ^ 2 - 1) * (1 - r) ^ 2) := by ring
    rw [e] at h9
    linarith only [h9, h4]
  have hσ3 : σ ≤ Sy ^ 2 / 3 := sig_le y1 y2 y3
  have hkey : 9 * (4 * r ^ 2 - 1) * Sy ^ 2 * σ ≤ 3 * σ := mul_le_mul_of_nonneg_right hnum hσ0
  have hfin : 0 ≤ t * (Sy * (5 * r - 3)) := mul_nonneg ht0.le (mul_nonneg hSy0 (by linarith only [hr]))
  have hS1 : Sy * Sy ≤ Sy * (t * (1 - r)) := mul_le_mul_of_nonneg_left hSy hSy0
  rw [hY2]
  nlinarith only [hwq, hkey, hσ3, hS1, hfin]



theorem mono_step {A p B L x : ℝ} (hL : 0 < L) (hx : L ≤ x) (hp : 0 ≤ p) (hB : 0 ≤ B)
    (h : 0 ≤ A * L + 36 * p * L ^ 2 - B) : 0 ≤ A * x + 36 * p * x ^ 2 - B := by
  have hx0 : 0 ≤ x := by linarith
  have h1 : 0 ≤ (x - L) * (36 * p * x * L + B) := mul_nonneg (by linarith) (by positivity)
  have h2 : 0 ≤ x * (A * L + 36 * p * L ^ 2 - B) := mul_nonneg (by linarith) h
  have h3 : L * (A * x + 36 * p * x ^ 2 - B) = x * (A * L + 36 * p * L ^ 2 - B) + (x - L) * (36 * p * x * L + B) := by ring
  by_contra hneg
  push Not at hneg
  have := mul_neg_of_pos_of_neg hL hneg
  linarith

/-- The first reduction of `X`: with weights `w_j ≥ D_j^+` bounded by `w`. -/
theorem X_first {p a1 a2 a3 e1 e2 e3 w1 w2 w3 w : ℝ}
    (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2) (ha3 : 0 ≤ a3) (he1 : 0 ≤ e1) (he2 : 0 ≤ e2) (he3 : 0 ≤ e3)
    (hp : 0 ≤ p) (hw1 : w1 ≤ w) (hw2 : w2 ≤ w) (hw3 : w3 ≤ w) :
    (18 * p * (2 * (p + a1 + e1) - 1) - 1) * a1 + (18 * p * (2 * (p + a2 + e2) - 1) - 1) * a2 +
      (18 * p * (2 * (p + a3 + e3) - 1) - 1) * a3 - 36 * (w1 * (a2 * a3) + w2 * (a1 * a3) + w3 * (a1 * a2)) ≥
    (18 * p * (2 * p - 1) - 1) * (a1 + a2 + a3) + 36 * p * (a1 + a2 + a3) ^ 2 -
      36 * (2 * p + w) * (a1 * a2 + a1 * a3 + a2 * a3) := by
  have h1 : w1 * (a2 * a3) ≤ w * (a2 * a3) := mul_le_mul_of_nonneg_right hw1 (mul_nonneg ha2 ha3)
  have h2 : w2 * (a1 * a3) ≤ w * (a1 * a3) := mul_le_mul_of_nonneg_right hw2 (mul_nonneg ha1 ha3)
  have h3 : w3 * (a1 * a2) ≤ w * (a1 * a2) := mul_le_mul_of_nonneg_right hw3 (mul_nonneg ha1 ha2)
  have g1 : 0 ≤ 36 * p * (a1 * e1) := by positivity
  have g2 : 0 ≤ 36 * p * (a2 * e2) := by positivity
  have g3 : 0 ≤ 36 * p * (a3 * e3) := by positivity
  nlinarith only [h1, h2, h3, g1, g2, g3]

/-- Case `r ≥ 19/25`. -/
theorem X_caseA {p a1 a2 a3 e1 e2 e3 : ℝ}
    (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2) (ha3 : 0 ≤ a3) (he1 : 0 ≤ e1) (he2 : 0 ≤ e2) (he3 : 0 ≤ e3)
    (hp : 361 / 625 ≤ p) (hN : p + (a1 + e1) + (a2 + e2) + (a3 + e3) = 1) :
    0 ≤ (18 * p * (2 * (p + a1 + e1) - 1) - 1) * a1 + (18 * p * (2 * (p + a2 + e2) - 1) - 1) * a2 +
      (18 * p * (2 * (p + a3 + e3) - 1) - 1) * a3 - 36 * ((2 * (p + a1 + e1) - 1) * (a2 * a3) +
        (2 * (p + a2 + e2) - 1) * (a1 * a3) + (2 * (p + a3 + e3) - 1) * (a1 * a2)) := by
  set X2 := a1 + a2 + a3 with hX2
  set q4 := a1 * a2 + a1 * a3 + a2 * a3 with hq4
  have hX2n : 0 ≤ X2 := by positivity
  have hq4n : 0 ≤ q4 := by positivity
  -- D_j ≤ 1 - 2(a_k + a_l)
  have hD1 : 2 * (p + a1 + e1) - 1 ≤ 1 - 2 * (a2 + a3) := by linarith only [hN, he2, he3]
  have hD2 : 2 * (p + a2 + e2) - 1 ≤ 1 - 2 * (a1 + a3) := by linarith only [hN, he1, he3]
  have hD3 : 2 * (p + a3 + e3) - 1 ≤ 1 - 2 * (a1 + a2) := by linarith only [hN, he1, he2]
  have hsum : (2 * (p + a1 + e1) - 1) * (a2 * a3) + (2 * (p + a2 + e2) - 1) * (a1 * a3) +
      (2 * (p + a3 + e3) - 1) * (a1 * a2) ≤
      (1 - 2 * (a2 + a3)) * (a2 * a3) + (1 - 2 * (a1 + a3)) * (a1 * a3) + (1 - 2 * (a1 + a2)) * (a1 * a2) := by
    have h1 := mul_le_mul_of_nonneg_right hD1 (mul_nonneg ha2 ha3)
    have h2 := mul_le_mul_of_nonneg_right hD2 (mul_nonneg ha1 ha3)
    have h3 := mul_le_mul_of_nonneg_right hD3 (mul_nonneg ha1 ha2)
    linarith only [h1, h2, h3]
  have hamgm : 9 * (a1 * a2 * a3) ≤ X2 * q4 := by
    rw [hX2, hq4]
    nlinarith only [mul_nonneg ha1 (sq_nonneg (a2 - a3)), mul_nonneg ha2 (sq_nonneg (a1 - a3)),
      mul_nonneg ha3 (sq_nonneg (a1 - a2))]
  have hsum2 : (1 - 2 * (a2 + a3)) * (a2 * a3) + (1 - 2 * (a1 + a3)) * (a1 * a3) + (1 - 2 * (a1 + a2)) * (a1 * a2) ≤
      (1 - 4 / 3 * X2) * q4 := by
    have e : (1 - 2 * (a2 + a3)) * (a2 * a3) + (1 - 2 * (a1 + a3)) * (a1 * a3) + (1 - 2 * (a1 + a2)) * (a1 * a2) =
        q4 - 2 * X2 * q4 + 6 * (a1 * a2 * a3) := by rw [hX2, hq4]; ring
    rw [e]; nlinarith only [hamgm]
  have hq43 : q4 ≤ X2 ^ 2 / 3 := by
    rw [hX2, hq4]; nlinarith only [sq_nonneg (a1 - a2), sq_nonneg (a1 - a3), sq_nonneg (a2 - a3)]
  have hX2le : X2 ≤ 1 - p := by rw [hX2]; linarith only [hN, he1, he2, he3]
  have hcoef : 0 ≤ 72 * p + 36 - 48 * X2 := by nlinarith only [hX2le, hp]
  -- main
  have hX : (18 * p * (2 * (p + a1 + e1) - 1) - 1) * a1 + (18 * p * (2 * (p + a2 + e2) - 1) - 1) * a2 +
      (18 * p * (2 * (p + a3 + e3) - 1) - 1) * a3 - 36 * ((2 * (p + a1 + e1) - 1) * (a2 * a3) +
        (2 * (p + a2 + e2) - 1) * (a1 * a3) + (2 * (p + a3 + e3) - 1) * (a1 * a2)) ≥
      (18 * p * (2 * p - 1) - 1) * X2 + 36 * p * (X2 ^ 2 - 2 * q4) - 36 * (1 - 4 / 3 * X2) * q4 := by
    have g1 : 0 ≤ 36 * p * (a1 * e1) := by positivity
    have g2 : 0 ≤ 36 * p * (a2 * e2) := by positivity
    have g3 : 0 ≤ 36 * p * (a3 * e3) := by positivity
    have hX2sq : X2 ^ 2 - 2 * q4 = a1 ^ 2 + a2 ^ 2 + a3 ^ 2 := by rw [hX2, hq4]; ring
    rw [hX2sq]
    nlinarith only [hsum, hsum2, g1, g2, g3]
  have hlow : (18 * p * (2 * p - 1) - 1) * X2 + 36 * p * (X2 ^ 2 - 2 * q4) - 36 * (1 - 4 / 3 * X2) * q4 ≥
      X2 * (18 * p * (2 * p - 1) - 1 - 12 * (1 - p) * X2 + 16 * X2 ^ 2) := by
    have := mul_le_mul_of_nonneg_right hq43 hcoef
    nlinarith only [this]
  have hsq : 0 ≤ 18 * p * (2 * p - 1) - 1 - 12 * (1 - p) * X2 + 16 * X2 ^ 2 := by
    nlinarith only [sq_nonneg (4 * X2 - 3 / 2 * (1 - p)), hp]
  nlinarith only [hX, hlow, mul_nonneg hX2n hsq]

/-- P1 ≥ 0 on [3/5,16/25] -/
theorem P1_pos {r : ℝ} (h0 : 3 / 5 ≤ r) (h1 : r ≤ 16 / 25) :
    0 ≤ -61368 * r ^ 6 / 5 + 118056 * r ^ 5 / 5 - 72618 * r ^ 4 / 5 + 756 * r ^ 3 + 2689 * r ^ 2 - 1054 * r + 120 := by
  obtain ⟨u, hu⟩ : ∃ u, u = r - 3 / 5 := ⟨_, rfl⟩
  have hu0 : 0 ≤ u := by linarith
  have hu1 : u ≤ 1 / 25 := by linarith
  have hr : r = u + 3 / 5 := by linarith
  subst hr
  have e : -61368 * (u + 3 / 5) ^ 6 / 5 + 118056 * (u + 3 / 5) ^ 5 / 5 - 72618 * (u + 3 / 5) ^ 4 / 5 + 756 * (u + 3 / 5) ^ 3 + 2689 * (u + 3 / 5) ^ 2 - 1054 * (u + 3 / 5) + 120 =
      -61368 / 5 * u ^ 6 - 514344 / 25 * u ^ 5 - 249186 / 25 * u ^ 4 - 265284 / 125 * u ^ 3 - 113039 / 625 * u ^ 2 + 227756 / 15625 * u + 3693 / 78125 := by ring
  rw [e]
  have u2 : u ^ 2 ≤ u / 25 := by nlinarith
  have u3 : u ^ 3 ≤ u / 625 := by nlinarith [sq_nonneg u, mul_nonneg hu0 hu0]
  have u4 : u ^ 4 ≤ u / 15625 := by nlinarith [pow_nonneg hu0 3, mul_nonneg hu0 hu0]
  have u5 : u ^ 5 ≤ u / 390625 := by nlinarith [pow_nonneg hu0 4, mul_nonneg hu0 hu0]
  have u6 : u ^ 6 ≤ u / 9765625 := by nlinarith [pow_nonneg hu0 5, mul_nonneg hu0 hu0]
  nlinarith

/-- P2 ≥ 0 on [16/25,19/25] -/
theorem P2_pos {r : ℝ} (h0 : 16 / 25 ≤ r) (h1 : r ≤ 19 / 25) :
    0 ≤ 72 * r ^ 5 - 432 * r ^ 4 + 432 * r ^ 3 - 54 * r ^ 2 - 52 * r + 7 := by
  have hh : 0 ≤ (r - 16 / 25) * (19 / 25 - r) := mul_nonneg (by linarith) (by linarith)
  have hS : 72 * r ^ 3 - 1656 * r ^ 2 / 5 - 41688 * r / 625 + 42858 / 3125 ≤ 0 := by
    nlinarith [mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 h1), sq_nonneg r]
  nlinarith [mul_nonneg hh (neg_nonneg.2 hS)]


/-- The two bounds `D_j^+ ≤ w`, `q₄ ≤ ¼(2r-1)⁴` give the reduced bound. -/
theorem X_caseB_core {r a1 a2 a3 e1 e2 e3 w1 w2 w3 w : ℝ}
    (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2) (ha3 : 0 ≤ a3) (he1 : 0 ≤ e1) (he2 : 0 ≤ e2) (he3 : 0 ≤ e3)
    (hw1 : w1 ≤ w) (hw2 : w2 ≤ w) (hw3 : w3 ≤ w)
    (hq : a1 * a2 + a1 * a3 + a2 * a3 ≤ (2 * r - 1) ^ 4 / 4) (hw0 : 0 ≤ w) :
    (18 * r ^ 2 * (2 * (r ^ 2 + a1 + e1) - 1) - 1) * a1 + (18 * r ^ 2 * (2 * (r ^ 2 + a2 + e2) - 1) - 1) * a2 +
      (18 * r ^ 2 * (2 * (r ^ 2 + a3 + e3) - 1) - 1) * a3 -
        36 * (w1 * (a2 * a3) + w2 * (a1 * a3) + w3 * (a1 * a2)) ≥
    (18 * r ^ 2 * (2 * r ^ 2 - 1) - 1) * (a1 + a2 + a3) + 36 * r ^ 2 * (a1 + a2 + a3) ^ 2 -
      9 * (2 * r ^ 2 + w) * (2 * r - 1) ^ 4 := by
  have h := X_first (p := r ^ 2) ha1 ha2 ha3 he1 he2 he3 (by positivity) hw1 hw2 hw3
  have hc : 0 ≤ 36 * (2 * r ^ 2 + w) := by positivity
  have := mul_le_mul_of_nonneg_left hq hc
  nlinarith only [h, this]

theorem X_caseB1 {r a1 a2 a3 e1 e2 e3 w1 w2 w3 : ℝ} (hr : 3 / 5 ≤ r) (hr1 : r ≤ 16 / 25)
    (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2) (ha3 : 0 ≤ a3) (he1 : 0 ≤ e1) (he2 : 0 ≤ e2) (he3 : 0 ≤ e3)
    (hw1 : w1 ≤ 4 * r ^ 2 - 1) (hw2 : w2 ≤ 4 * r ^ 2 - 1) (hw3 : w3 ≤ 4 * r ^ 2 - 1)
    (hq : a1 * a2 + a1 * a3 + a2 * a3 ≤ (2 * r - 1) ^ 4 / 4)
    (hL : 1 / 15 * (1 - r) * (15 - 11 * r) ≤ a1 + a2 + a3) :
    0 ≤ (18 * r ^ 2 * (2 * (r ^ 2 + a1 + e1) - 1) - 1) * a1 + (18 * r ^ 2 * (2 * (r ^ 2 + a2 + e2) - 1) - 1) * a2 +
      (18 * r ^ 2 * (2 * (r ^ 2 + a3 + e3) - 1) - 1) * a3 -
        36 * (w1 * (a2 * a3) + w2 * (a1 * a3) + w3 * (a1 * a2)) := by
  have hw0 : 0 ≤ 4 * r ^ 2 - 1 := by nlinarith only [hr]
  have h := X_caseB_core ha1 ha2 ha3 he1 he2 he3 hw1 hw2 hw3 hq hw0
  have hLpos : 0 < 1 / 15 * (1 - r) * (15 - 11 * r) := by
    have : 0 < 1 - r := by linarith only [hr1]
    have : 0 < 15 - 11 * r := by linarith only [hr1]
    positivity
  have hB : 0 ≤ 9 * (2 * r ^ 2 + (4 * r ^ 2 - 1)) * (2 * r - 1) ^ 4 := by
    have : 0 ≤ 2 * r ^ 2 + (4 * r ^ 2 - 1) := by nlinarith only [hr]
    positivity
  have hP := P1_pos hr hr1
  have hh : 0 ≤ (18 * r ^ 2 * (2 * r ^ 2 - 1) - 1) * (1 / 15 * (1 - r) * (15 - 11 * r)) +
      36 * r ^ 2 * (1 / 15 * (1 - r) * (15 - 11 * r)) ^ 2 - 9 * (2 * r ^ 2 + (4 * r ^ 2 - 1)) * (2 * r - 1) ^ 4 := by
    nlinarith only [hP]
  have hm := mono_step (A := 18 * r ^ 2 * (2 * r ^ 2 - 1) - 1) (p := r ^ 2) hLpos hL (by positivity) hB hh
  nlinarith only [h, hm]

theorem X_caseB2 {r a1 a2 a3 e1 e2 e3 w1 w2 w3 : ℝ} (hr : 16 / 25 ≤ r) (hr1 : r ≤ 19 / 25)
    (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2) (ha3 : 0 ≤ a3) (he1 : 0 ≤ e1) (he2 : 0 ≤ e2) (he3 : 0 ≤ e3)
    (hw1 : w1 ≤ 1) (hw2 : w2 ≤ 1) (hw3 : w3 ≤ 1)
    (hq : a1 * a2 + a1 * a3 + a2 * a3 ≤ (2 * r - 1) ^ 4 / 4)
    (hL : 2 * (1 - r) * (2 * r - 1) ≤ a1 + a2 + a3) :
    0 ≤ (18 * r ^ 2 * (2 * (r ^ 2 + a1 + e1) - 1) - 1) * a1 + (18 * r ^ 2 * (2 * (r ^ 2 + a2 + e2) - 1) - 1) * a2 +
      (18 * r ^ 2 * (2 * (r ^ 2 + a3 + e3) - 1) - 1) * a3 -
        36 * (w1 * (a2 * a3) + w2 * (a1 * a3) + w3 * (a1 * a2)) := by
  have h := X_caseB_core ha1 ha2 ha3 he1 he2 he3 hw1 hw2 hw3 hq (by norm_num : (0:ℝ) ≤ 1)
  have hLpos : 0 < 2 * (1 - r) * (2 * r - 1) := by
    have : 0 < 1 - r := by linarith only [hr1]
    have : 0 < 2 * r - 1 := by linarith only [hr]
    positivity
  have hB : 0 ≤ 9 * (2 * r ^ 2 + 1) * (2 * r - 1) ^ 4 := by positivity
  have hP := P2_pos hr hr1
  have h2r : 0 ≤ 2 * r - 1 := by linarith only [hr]
  have hh : 0 ≤ (18 * r ^ 2 * (2 * r ^ 2 - 1) - 1) * (2 * (1 - r) * (2 * r - 1)) +
      36 * r ^ 2 * (2 * (1 - r) * (2 * r - 1)) ^ 2 - 9 * (2 * r ^ 2 + 1) * (2 * r - 1) ^ 4 := by
    have e : (18 * r ^ 2 * (2 * r ^ 2 - 1) - 1) * (2 * (1 - r) * (2 * r - 1)) +
        36 * r ^ 2 * (2 * (1 - r) * (2 * r - 1)) ^ 2 - 9 * (2 * r ^ 2 + 1) * (2 * r - 1) ^ 4 =
        (2 * r - 1) * (72 * r ^ 5 - 432 * r ^ 4 + 432 * r ^ 3 - 54 * r ^ 2 - 52 * r + 7) := by ring
    rw [e]; exact mul_nonneg h2r hP
  have hm := mono_step (A := 18 * r ^ 2 * (2 * r ^ 2 - 1) - 1) (p := r ^ 2) hLpos hL (by positivity) hB hh
  nlinarith only [h, hm]


/-- **`X ≥ 0`** (the `x`-part of the decoupled bound, `CO-2`). -/
theorem X_nonneg {r a1 a2 a3 e1 e2 e3 : ℝ} (hr : 3 / 5 ≤ r) (hr1 : r ≤ 1)
    (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2) (ha3 : 0 ≤ a3) (he1 : 0 ≤ e1) (he2 : 0 ≤ e2) (he3 : 0 ≤ e3)
    (hN : r ^ 2 + (a1 + e1) + (a2 + e2) + (a3 + e3) = 1)
    (hp1 : a1 + e1 ≤ r ^ 2) (hp2 : a2 + e2 ≤ r ^ 2) (hp3 : a3 + e3 ≤ r ^ 2)
    (hL1 : 1 / 15 * (1 - r) * (15 - 11 * r) ≤ a1 + a2 + a3) (hL2 : 2 * (1 - r) * (2 * r - 1) ≤ a1 + a2 + a3)
    (hq : a1 * a2 + a1 * a3 + a2 * a3 ≤ (2 * r - 1) ^ 4 / 4) :
    0 ≤ (18 * r ^ 2 * (2 * (r ^ 2 + a1 + e1) - 1) - 1) * a1 + (18 * r ^ 2 * (2 * (r ^ 2 + a2 + e2) - 1) - 1) * a2 +
      (18 * r ^ 2 * (2 * (r ^ 2 + a3 + e3) - 1) - 1) * a3 -
        36 * (max (2 * (r ^ 2 + a1 + e1) - 1) 0 * (a2 * a3) + max (2 * (r ^ 2 + a2 + e2) - 1) 0 * (a1 * a3) +
          max (2 * (r ^ 2 + a3 + e3) - 1) 0 * (a1 * a2)) := by
  by_cases hX2 : a1 + a2 + a3 = 0
  · have h1 : a1 = 0 := by linarith only [hX2, ha1, ha2, ha3]
    have h2 : a2 = 0 := by linarith only [hX2, ha1, ha2, ha3]
    have h3 : a3 = 0 := by linarith only [hX2, ha1, ha2, ha3]
    subst h1 h2 h3
    simp
  · have hX2pos : 0 < a1 + a2 + a3 := lt_of_le_of_ne (by positivity) (Ne.symm hX2)
    rcases le_or_gt (19 / 25) r with hA | hB
    · have hp : 361 / 625 ≤ r ^ 2 := by nlinarith only [hA]
      have hD1 : 0 ≤ 2 * (r ^ 2 + a1 + e1) - 1 := by linarith only [hp, ha1, he1]
      have hD2 : 0 ≤ 2 * (r ^ 2 + a2 + e2) - 1 := by linarith only [hp, ha2, he2]
      have hD3 : 0 ≤ 2 * (r ^ 2 + a3 + e3) - 1 := by linarith only [hp, ha3, he3]
      rw [max_eq_left hD1, max_eq_left hD2, max_eq_left hD3]
      exact X_caseA ha1 ha2 ha3 he1 he2 he3 hp hN
    · have hD1u : 2 * (r ^ 2 + a1 + e1) - 1 ≤ 1 := by linarith only [hN, ha2, ha3, he2, he3]
      have hD2u : 2 * (r ^ 2 + a2 + e2) - 1 ≤ 1 := by linarith only [hN, ha1, ha3, he1, he3]
      have hD3u : 2 * (r ^ 2 + a3 + e3) - 1 ≤ 1 := by linarith only [hN, ha1, ha2, he1, he2]
      rcases le_or_gt r (16 / 25) with hB1 | hB2
      · have h4 : 0 ≤ 4 * r ^ 2 - 1 := by nlinarith only [hr]
        have w1 : max (2 * (r ^ 2 + a1 + e1) - 1) 0 ≤ 4 * r ^ 2 - 1 :=
          max_le (by linarith only [hp1]) h4
        have w2 : max (2 * (r ^ 2 + a2 + e2) - 1) 0 ≤ 4 * r ^ 2 - 1 :=
          max_le (by linarith only [hp2]) h4
        have w3 : max (2 * (r ^ 2 + a3 + e3) - 1) 0 ≤ 4 * r ^ 2 - 1 :=
          max_le (by linarith only [hp3]) h4
        exact X_caseB1 hr hB1 ha1 ha2 ha3 he1 he2 he3 w1 w2 w3 hq hL1
      · have w1 : max (2 * (r ^ 2 + a1 + e1) - 1) 0 ≤ 1 := max_le hD1u (by norm_num)
        have w2 : max (2 * (r ^ 2 + a2 + e2) - 1) 0 ≤ 1 := max_le hD2u (by norm_num)
        have w3 : max (2 * (r ^ 2 + a3 + e3) - 1) 0 ≤ 1 := max_le hD3u (by norm_num)
        exact X_caseB2 hB2.le hB.le ha1 ha2 ha3 he1 he2 he3 w1 w2 w3 hq hL2


theorem pair_bound (D xk xl yk yl : ℝ) :
    -(18 * D * (xk * xl + yk * yl) ^ 2) ≥ -(36 * max D 0 * (xk ^ 2 * xl ^ 2 + yk ^ 2 * yl ^ 2)) := by
  have hc : (xk * xl + yk * yl) ^ 2 ≤ 2 * (xk ^ 2 * xl ^ 2 + yk ^ 2 * yl ^ 2) := by
    nlinarith only [sq_nonneg (xk * xl - yk * yl)]
  rcases le_or_gt 0 D with h | h
  · rw [max_eq_left h]
    nlinarith only [mul_le_mul_of_nonneg_left hc h]
  · rw [max_eq_right h.le]
    nlinarith only [mul_nonneg (neg_nonneg.2 h.le) (sq_nonneg (xk * xl + yk * yl))]

/-- **`Q + 2Φ_im - 3/2 ≥ 0`** in the normalised real coordinates (`CO-2`). -/
theorem core_real {t r x1 x2 x3 y1 y2 y3 : ℝ} (ht : t ^ 2 = 3) (ht0 : 0 < t) (hr0 : 0 < r)
    (hy1 : 0 ≤ y1) (hy2 : 0 ≤ y2) (hy3 : 0 ≤ y3)
    (hN : r ^ 2 + (x1 ^ 2 + y1 ^ 2) + (x2 ^ 2 + y2 ^ 2) + (x3 ^ 2 + y3 ^ 2) = 1)
    (hp1 : x1 ^ 2 + y1 ^ 2 ≤ r ^ 2) (hp2 : x2 ^ 2 + y2 ^ 2 ≤ r ^ 2) (hp3 : x3 ^ 2 + y3 ^ 2 ≤ r ^ 2)
    (hl : ∀ s1 s2 s3 : ℝ, s1 ^ 2 = 1 → s2 ^ 2 = 1 → s3 ^ 2 = 1 →
      (r + s1 * x1 + s2 * x2 + s3 * x3) ^ 2 + (s1 * y1 + s2 * y2 + s3 * y3) ^ 2 ≤ 4 * r ^ 2)
    (hΦ : r ^ 2 / 2 + (y1 + y2 + y3) ^ 2 / 6 + t * r * (y1 + y2 + y3) / 3 ≤ 1 / 2) :
    0 ≤ (1 / 2 + 18 * ((2 * (r ^ 2 + x1 ^ 2 + y1 ^ 2) - 1) * (r ^ 2 * x1 ^ 2 - (x2 * x3 + y2 * y3) ^ 2) +
        (2 * (r ^ 2 + x2 ^ 2 + y2 ^ 2) - 1) * (r ^ 2 * x2 ^ 2 - (x1 * x3 + y1 * y3) ^ 2) +
        (2 * (r ^ 2 + x3 ^ 2 + y3 ^ 2) - 1) * (r ^ 2 * x3 ^ 2 - (x1 * x2 + y1 * y2) ^ 2))) +
      2 * (r ^ 2 / 2 + (y1 + y2 + y3) ^ 2 / 6 + t * r * (y1 + y2 + y3) / 3) - 3 / 2 := by
  obtain ⟨hr1, hSy, hr35, hL1, hL2, hq⟩ := core_constraints ht ht0 hr0 hy1 hy2 hy3 hN hp1 hp2 hp3 hl hΦ
  have hxsq1 : 0 ≤ x1 ^ 2 := sq_nonneg x1
  have hxsq2 : 0 ≤ x2 ^ 2 := sq_nonneg x2
  have hxsq3 : 0 ≤ x3 ^ 2 := sq_nonneg x3
  have hysq1 : 0 ≤ y1 ^ 2 := sq_nonneg y1
  have hysq2 : 0 ≤ y2 ^ 2 := sq_nonneg y2
  have hysq3 : 0 ≤ y3 ^ 2 := sq_nonneg y3
  have hX := X_nonneg hr35 hr1 hxsq1 hxsq2 hxsq3 hysq1 hysq2 hysq3 hN hp1 hp2 hp3 hL1 hL2 hq
  have hr2 : 0 ≤ 4 * r ^ 2 - 1 := by nlinarith only [hr35]
  have hw1' : max (2 * (r ^ 2 + x1 ^ 2 + y1 ^ 2) - 1) 0 ≤ 4 * r ^ 2 - 1 :=
    max_le (by linarith only [hp1]) hr2
  have hw2' : max (2 * (r ^ 2 + x2 ^ 2 + y2 ^ 2) - 1) 0 ≤ 4 * r ^ 2 - 1 :=
    max_le (by linarith only [hp2]) hr2
  have hw3' : max (2 * (r ^ 2 + x3 ^ 2 + y3 ^ 2) - 1) 0 ≤ 4 * r ^ 2 - 1 :=
    max_le (by linarith only [hp3]) hr2
  have hY := Y_nonneg ht ht0 hr35 hr1 hy1 hy2 hy3 hSy (le_max_right _ _) (le_max_right _ _) (le_max_right _ _)
    hw1' hw2' hw3'
  have p1 := pair_bound (2 * (r ^ 2 + x1 ^ 2 + y1 ^ 2) - 1) x2 x3 y2 y3
  have p2 := pair_bound (2 * (r ^ 2 + x2 ^ 2 + y2 ^ 2) - 1) x1 x3 y1 y3
  have p3 := pair_bound (2 * (r ^ 2 + x3 ^ 2 + y3 ^ 2) - 1) x1 x2 y1 y2
  nlinarith only [hX, hY, p1, p2, p3, hN]

end FormalResearch.FourQubitEntropy.CO
