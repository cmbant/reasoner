import FormalResearch.FourQubitEntropy.RenyiFullPath

/-!
# The slope bound `η > ω` of `lem:fqe-low-tilt-reduction` and `lem:fqe-hs-tilt`: numerics

* `Z_le_E1`: `Σ nᵢ Eᵢ^q ≤ E₁^{q-1}` when `E₁ ≥ E₂ ≥ E₃ ≥ 0` and `Σ nᵢEᵢ = 1`.
* `Z_le_pur`: `Σ nᵢ Eᵢ^q ≤ (Σ nᵢ Eᵢ²)^{q-1}` (concavity of `x^r`).
* `ar_bound`: `a^r (1-a)^{2-r} ≤ 3/8` for `1/4 ≤ a ≤ 1/2`, `1/2 ≤ r ≤ 3/5`.
* `slope_of_bound`: the divided-difference bound turns into the slope bound.
* `lowTilt_slope_numeric`, `hsTilt_slope_numeric`: the two numerical comparisons
  `6 ω ln2 · Z < q(1-r) m^{r-2}` (`η > 64/35 > 9/5` and `η > 1`).
-/

namespace FormalResearch.FourQubitEntropy.RenyiFull

open Set

theorem rpow_eq_mul {x r : ℝ} (hx : 0 ≤ x) (hr : 0 < r) : x ^ (r + 1) = x * x ^ r := by
  rw [Real.rpow_add' hx (by linarith), Real.rpow_one, mul_comm]

theorem Z_le_E1 {q n1 n2 n3 E1 E2 E3 : ℝ} (hq : 1 < q) (hn1 : 0 ≤ n1) (hn2 : 0 ≤ n2)
    (hn3 : 0 ≤ n3) (h3 : 0 ≤ E3) (h32 : E3 ≤ E2) (h21 : E2 ≤ E1)
    (hs : n1 * E1 + n2 * E2 + n3 * E3 = 1) :
    n1 * E1 ^ q + n2 * E2 ^ q + n3 * E3 ^ q ≤ E1 ^ (q - 1) := by
  have h2 : 0 ≤ E2 := h3.trans h32
  have h1 : 0 ≤ E1 := h2.trans h21
  have hr : 0 < q - 1 := by linarith
  have e : ∀ E : ℝ, 0 ≤ E → E ^ q = E * E ^ (q - 1) := fun E hE => by
    have := rpow_eq_mul hE hr
    rwa [show q - 1 + 1 = q by ring] at this
  rw [e E1 h1, e E2 h2, e E3 h3]
  have m2 : E2 ^ (q - 1) ≤ E1 ^ (q - 1) := Real.rpow_le_rpow h2 h21 hr.le
  have m3 : E3 ^ (q - 1) ≤ E1 ^ (q - 1) := Real.rpow_le_rpow h3 (h32.trans h21) hr.le
  have p2 : 0 ≤ n2 * E2 := mul_nonneg hn2 h2
  have p3 : 0 ≤ n3 * E3 := mul_nonneg hn3 h3
  have hs' : (n1 * E1 + n2 * E2 + n3 * E3) * E1 ^ (q - 1) = E1 ^ (q - 1) := by rw [hs, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left m2 p2, mul_le_mul_of_nonneg_left m3 p3]

/-- Tangent line of the concave function `y ↦ y^r`. -/
theorem rpow_concave_tangent {r p y : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hp : 0 < p) (hy : 0 ≤ y) :
    y ^ r ≤ p ^ r + r * p ^ (r - 1) * (y - p) := by
  have hs : (-1 : ℝ) ≤ y / p - 1 := by
    have : 0 ≤ y / p := div_nonneg hy hp.le
    linarith
  have hb := rpow_one_add_le_one_add_mul_self hs hr0 hr1
  rw [show 1 + (y / p - 1) = y / p by ring, Real.div_rpow hy hp.le] at hb
  have hpr : 0 < p ^ r := Real.rpow_pos_of_pos hp _
  have e : p ^ (r - 1) = p ^ r / p := by
    rw [Real.rpow_sub hp, Real.rpow_one]
  rw [e]
  have h2 : y ^ r = p ^ r * (y ^ r / p ^ r) := by field_simp
  rw [h2]
  have h3 : p ^ r + r * (p ^ r / p) * (y - p) = p ^ r * (1 + r * (y / p - 1)) := by
    field_simp
  rw [h3]
  exact mul_le_mul_of_nonneg_left hb hpr.le

theorem Z_le_pur {q n1 n2 n3 E1 E2 E3 : ℝ} (hq : 1 < q) (hq2 : q ≤ 2) (hn1 : 0 ≤ n1)
    (hn2 : 0 ≤ n2) (hn3 : 0 ≤ n3) (h1 : 0 ≤ E1) (h2 : 0 ≤ E2) (h3 : 0 ≤ E3)
    (hs : n1 * E1 + n2 * E2 + n3 * E3 = 1) {p : ℝ} (hp : p = n1 * E1 ^ 2 + n2 * E2 ^ 2 + n3 * E3 ^ 2) :
    n1 * E1 ^ q + n2 * E2 ^ q + n3 * E3 ^ q ≤ p ^ (q - 1) := by
  have hr : 0 < q - 1 := by linarith
  have hr1 : q - 1 ≤ 1 := by linarith
  have hpp : 0 < p := by
    -- p ≥ 1/4 · (Σ nᵢEᵢ)² is not needed; positivity from Σ nᵢ Eᵢ = 1
    by_contra hnp
    push Not at hnp
    have a1 : n1 * E1 ^ 2 = 0 := by nlinarith [mul_nonneg hn1 (sq_nonneg E1), mul_nonneg hn2 (sq_nonneg E2), mul_nonneg hn3 (sq_nonneg E3)]
    have a2 : n2 * E2 ^ 2 = 0 := by nlinarith [mul_nonneg hn1 (sq_nonneg E1), mul_nonneg hn2 (sq_nonneg E2), mul_nonneg hn3 (sq_nonneg E3)]
    have a3 : n3 * E3 ^ 2 = 0 := by nlinarith [mul_nonneg hn1 (sq_nonneg E1), mul_nonneg hn2 (sq_nonneg E2), mul_nonneg hn3 (sq_nonneg E3)]
    have b1 : n1 * E1 = 0 := by
      rcases mul_eq_zero.1 a1 with h | h
      · simp [h]
      · have : E1 = 0 := by simpa using h
        simp [this]
    have b2 : n2 * E2 = 0 := by
      rcases mul_eq_zero.1 a2 with h | h
      · simp [h]
      · have : E2 = 0 := by simpa using h
        simp [this]
    have b3 : n3 * E3 = 0 := by
      rcases mul_eq_zero.1 a3 with h | h
      · simp [h]
      · have : E3 = 0 := by simpa using h
        simp [this]
    linarith
  have e : ∀ E : ℝ, 0 ≤ E → E ^ q = E * E ^ (q - 1) := fun E hE => by
    have := rpow_eq_mul hE hr
    rwa [show q - 1 + 1 = q by ring] at this
  have t1 := rpow_concave_tangent hr.le hr1 hpp h1
  have t2 := rpow_concave_tangent hr.le hr1 hpp h2
  have t3 := rpow_concave_tangent hr.le hr1 hpp h3
  rw [e E1 h1, e E2 h2, e E3 h3]
  have m1 := mul_le_mul_of_nonneg_left t1 (mul_nonneg hn1 h1)
  have m2 := mul_le_mul_of_nonneg_left t2 (mul_nonneg hn2 h2)
  have m3 := mul_le_mul_of_nonneg_left t3 (mul_nonneg hn3 h3)
  have key : n1 * (E1 * (p ^ (q - 1) + (q - 1) * p ^ (q - 1 - 1) * (E1 - p))) +
      n2 * (E2 * (p ^ (q - 1) + (q - 1) * p ^ (q - 1 - 1) * (E2 - p))) +
      n3 * (E3 * (p ^ (q - 1) + (q - 1) * p ^ (q - 1 - 1) * (E3 - p))) = p ^ (q - 1) := by
    have : n1 * (E1 * (p ^ (q - 1) + (q - 1) * p ^ (q - 1 - 1) * (E1 - p))) +
      n2 * (E2 * (p ^ (q - 1) + (q - 1) * p ^ (q - 1 - 1) * (E2 - p))) +
      n3 * (E3 * (p ^ (q - 1) + (q - 1) * p ^ (q - 1 - 1) * (E3 - p))) =
      p ^ (q - 1) * (n1 * E1 + n2 * E2 + n3 * E3) +
        (q - 1) * p ^ (q - 1 - 1) * ((n1 * E1 ^ 2 + n2 * E2 ^ 2 + n3 * E3 ^ 2) -
          p * (n1 * E1 + n2 * E2 + n3 * E3)) := by ring
    rw [this, hs, ← hp]; ring
  nlinarith [key, m1, m2, m3]

/-! ### Numerical bounds -/

theorem log_two_lt : Real.log 2 < 7 / 10 := by
  have := Real.log_two_lt_d9
  linarith

theorem ar_bound {a r : ℝ} (ha1 : 1 / 4 ≤ a) (ha2 : a ≤ 1 / 2) (hr1 : 1 / 2 ≤ r) (hr2 : r ≤ 3 / 5) :
    a ^ r * (1 - a) ^ (2 - r) ≤ 3 / 8 := by
  have ha : 0 < a := by linarith
  have hb : 0 < 1 - a := by linarith
  have e : a ^ r * (1 - a) ^ (2 - r) = Real.exp (r * Real.log a + (2 - r) * Real.log (1 - a)) := by
    rw [Real.rpow_def_of_pos ha, Real.rpow_def_of_pos hb, ← Real.exp_add]
    ring_nf
  have l2 : Real.log 2 < Real.log 3 := Real.log_lt_log (by norm_num) (by norm_num)
  have l4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have l8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  have q14 : Real.log (1 / 4) = -(2 * Real.log 2) := by
    rw [one_div, Real.log_inv, l4]
  have q34 : Real.log (3 / 4) = Real.log 3 - 2 * Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), l4]
  have q38 : Real.log (3 / 8) = Real.log 3 - 3 * Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), l8]
  have h1 : Real.log a + Real.log (1 - a) ≤ Real.log (1 / 4) := by
    rw [← Real.log_mul ha.ne' hb.ne']
    exact Real.log_le_log (by positivity) (by nlinarith [sq_nonneg (a - 1 / 2)])
  have h2 : Real.log (1 - a) ≤ Real.log (3 / 4) := Real.log_le_log hb (by linarith)
  have key : r * Real.log a + (2 - r) * Real.log (1 - a) ≤ Real.log (3 / 8) := by
    have : r * Real.log a + (2 - r) * Real.log (1 - a) =
        r * (Real.log a + Real.log (1 - a)) + (2 - 2 * r) * Real.log (1 - a) := by ring
    rw [this]
    have m1 := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ r)
    have m2 := mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ 2 - 2 * r)
    rw [q14] at m1
    rw [q34] at m2
    rw [q38]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * r - 1) (sub_nonneg.2 l2.le)]
  rw [e]
  calc Real.exp (r * Real.log a + (2 - r) * Real.log (1 - a)) ≤ Real.exp (Real.log (3 / 8)) :=
        Real.exp_le_exp.2 key
    _ = 3 / 8 := Real.exp_log (by norm_num)

theorem slope_of_bound {q ω L Z D S : ℝ} (hq : 1 < q) (hL : 0 < L) (hZ : 0 < Z) (hS : S ≤ -D)
    (hlt : 3 * ω * ((q - 1) * L * Z) < q * S) :
    3 * ω < q * (-D) / ((q - 1) * L * Z) := by
  have hq1 : 0 < q - 1 := by linarith
  have hden : 0 < (q - 1) * L * Z := by positivity
  rw [lt_div_iff₀ hden]
  nlinarith [mul_le_mul_of_nonneg_left hS (by linarith : (0 : ℝ) ≤ q)]

/-- `3^{7/5} > 9/2`. -/
theorem three_pow_gt : (9 / 2 : ℝ) < (3 : ℝ) ^ (7 / 5 : ℝ) := by
  have h5 : ((3 : ℝ) ^ (7 / 5 : ℝ)) ^ (5 : ℕ) = 2187 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  by_contra hle
  push Not at hle
  have hpos : 0 ≤ (3 : ℝ) ^ (7 / 5 : ℝ) := by positivity
  have := pow_le_pow_left₀ hpos hle 5
  rw [h5] at this
  norm_num at this

theorem three_pow_ge {r : ℝ} (hr : r ≤ 3 / 5) : (9 / 2 : ℝ) < (3 : ℝ) ^ (2 - r) :=
  three_pow_gt.trans_le (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith))

/-- `((1-a)/3)^{r-2} (1-a)^{2-r} = 3^{2-r}`. -/
theorem mean_pow_mul {a r : ℝ} (ha : a < 1) :
    ((1 - a) / 3) ^ (r - 2) * (1 - a) ^ (2 - r) = (3 : ℝ) ^ (2 - r) := by
  have hb : 0 < 1 - a := by linarith
  rw [Real.div_rpow hb.le (by norm_num), div_mul_eq_mul_div, mul_comm ((1 - a) ^ (r - 2)),
    ← Real.rpow_add hb]
  rw [show 2 - r + (r - 2) = 0 by ring, Real.rpow_zero,
    show r - 2 = -(2 - r) by ring, Real.rpow_neg (by norm_num)]
  simp

/-- **Low-tilt numerics.** `q ∈ [3/2, 8/5]`, `ω ≤ 9/5`, `1/4 ≤ a ≤ 1/2`, `Z ≤ a^{q-1}`:
`6 ω ln2 · Z < q (2-q) ((1-a)/3)^{q-3}` (the paper's `η > 64/35 > 9/5`). -/
theorem lowTilt_slope_numeric {q ω a Z : ℝ} (hq1 : 3 / 2 ≤ q) (hq2 : q ≤ 8 / 5) (hω0 : 0 ≤ ω)
    (hω1 : ω ≤ 9 / 5) (ha1 : 1 / 4 ≤ a) (ha2 : a ≤ 1 / 2) (hZ : 0 < Z) (hZa : Z ≤ a ^ (q - 1)) :
    6 * ω * Real.log 2 * Z < q * (1 - (q - 1)) * ((1 - a) / 3) ^ (q - 1 - 2) := by
  set r := q - 1 with hr
  have hr1 : 1 / 2 ≤ r := by linarith
  have hr2 : r ≤ 3 / 5 := by linarith
  have hb : 0 < (1 - a) ^ (2 - r) := Real.rpow_pos_of_pos (by linarith) _
  have hL0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL1 := log_two_lt
  have hA := ar_bound ha1 ha2 hr1 hr2
  have hM := mean_pow_mul (a := a) (r := r) (by linarith)
  have h3 := three_pow_ge hr2
  have hqr : 16 / 25 ≤ q * (1 - r) := by rw [hr]; nlinarith
  have hLZ : 6 * ω * Real.log 2 * Z ≤ 6 * (9 / 5) * (7 / 10) * a ^ r := by
    have h1 : ω * Real.log 2 ≤ 9 / 5 * (7 / 10) :=
      mul_le_mul hω1 hL1.le hL0.le (by norm_num)
    have h2 : (ω * Real.log 2) * Z ≤ (9 / 5 * (7 / 10)) * a ^ r :=
      mul_le_mul h1 hZa hZ.le (by norm_num)
    nlinarith
  have key : (6 * (9 / 5) * (7 / 10) * a ^ r) * (1 - a) ^ (2 - r) <
      (q * (1 - r) * ((1 - a) / 3) ^ (r - 2)) * (1 - a) ^ (2 - r) := by
    have e : (q * (1 - r) * ((1 - a) / 3) ^ (r - 2)) * (1 - a) ^ (2 - r) =
        q * (1 - r) * (3 : ℝ) ^ (2 - r) := by rw [mul_assoc, hM]
    rw [e]
    have : (6 * (9 / 5) * (7 / 10) * a ^ r) * (1 - a) ^ (2 - r) ≤ 6 * (9 / 5) * (7 / 10) * (3 / 8) := by
      have := mul_le_mul_of_nonneg_left hA (by norm_num : (0 : ℝ) ≤ 6 * (9 / 5) * (7 / 10))
      linarith
    nlinarith
  have := lt_of_mul_lt_mul_right key hb.le
  linarith

/-- **HS-tilt numerics** (`q = 8/5`, `ω = 1`): `Z ≤ p^{3/5}`, `p ≤ 9/16`, `0 < m ≤ 1/3`:
`6 ln2 · Z < (8/5)(2/5) m^{-7/5}` (the paper's `η > 1`). -/
theorem hsTilt_slope_numeric {p Z m : ℝ} (hp : p ≤ 9 / 16) (hp0 : 0 < p) (hZ : 0 < Z)
    (hZp : Z ≤ p ^ ((8 / 5 : ℝ) - 1)) (hm0 : 0 < m) (hm : m ≤ 1 / 3) :
    6 * 1 * Real.log 2 * Z < 8 / 5 * (1 - ((8 / 5 : ℝ) - 1)) * m ^ ((8 / 5 : ℝ) - 1 - 2) := by
  have hL0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL1 := log_two_lt
  have hr : (8 / 5 : ℝ) - 1 = 3 / 5 := by norm_num
  rw [hr] at hZp ⊢
  have h1 : p ^ (3 / 5 : ℝ) ≤ (9 / 16 : ℝ) ^ (3 / 5 : ℝ) :=
    Real.rpow_le_rpow hp0.le hp (by norm_num)
  have h2 : (1 / 3 : ℝ) ^ ((3 / 5 : ℝ) - 2) ≤ m ^ ((3 / 5 : ℝ) - 2) :=
    Real.rpow_le_rpow_of_nonpos hm0 hm (by norm_num)
  have h3 : (1 / 3 : ℝ) ^ ((3 / 5 : ℝ) - 2) = (3 : ℝ) ^ (7 / 5 : ℝ) := by
    rw [one_div, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num)]
    norm_num
  have hX5 : ((9 / 16 : ℝ) ^ (3 / 5 : ℝ)) ^ (5 : ℕ) = 729 / 4096 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  have hY5 : ((3 : ℝ) ^ (7 / 5 : ℝ)) ^ (5 : ℕ) = 2187 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  have hXY : (9 / 16 : ℝ) ^ (3 / 5 : ℝ) * (105 / 16) < (3 : ℝ) ^ (7 / 5 : ℝ) := by
    by_contra hle
    push Not at hle
    have hpos : 0 ≤ (3 : ℝ) ^ (7 / 5 : ℝ) := by positivity
    have := pow_le_pow_left₀ hpos hle 5
    rw [hY5, mul_pow, hX5] at this
    norm_num at this
  have hX0 : 0 < (9 / 16 : ℝ) ^ (3 / 5 : ℝ) := by positivity
  have hZX : Z ≤ (9 / 16 : ℝ) ^ (3 / 5 : ℝ) := hZp.trans h1
  have hLZ : Real.log 2 * Z ≤ 7 / 10 * (9 / 16 : ℝ) ^ (3 / 5 : ℝ) :=
    mul_le_mul hL1.le hZX hZ.le (by norm_num)
  rw [h3] at h2
  norm_num
  nlinarith

/-- info: 'FormalResearch.FourQubitEntropy.RenyiFull.lowTilt_slope_numeric' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lowTilt_slope_numeric

/-- info: 'FormalResearch.FourQubitEntropy.RenyiFull.hsTilt_slope_numeric' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hsTilt_slope_numeric

end FormalResearch.FourQubitEntropy.RenyiFull
