import Mathlib

/-!
# Sharp third-moment bound at fixed purity

If a four-point probability vector has purity `p = 1/4 + x`, then `0 ≤ x ≤ 3/4` and
`|t - 1/16 - 3x/4| ≤ x^{3/2}/√3` where `t = Σ λᵢ³`. The upper bound is attained only at the
one-large spectrum `((1+3s)/4, (1-s)/4, (1-s)/4, (1-s)/4)` (up to permutation), `s = √(4x/3)`;
the lower bound only at the one-small spectrum `((1-3s)/4, (1+s)/4, (1+s)/4, (1+s)/4)`, which is a
probability vector exactly when `x ≤ 1/12`.

Paper: `lem:fqe-third-moment` (renyi_uncapped_covering.tex).

The paper optimises the cubic on a round two-sphere; here the same extremal values are certified by
the cubic identity `3r³ - Σ wᵢ³ = Σ (wᵢ + r/2)²(3r/2 - wᵢ)` (with `wᵢ = λᵢ - 1/4`, `x = 3r²`) together
with the bound `wᵢ ≤ 3r/2`, whose equality set is exactly the one-large pattern.
-/

namespace FormalResearch.FourQubitEntropy

open Real

/-- The one-large spectrum with parameter `s`. -/
noncomputable def oneLarge (s : ℝ) (i : Fin 4) : Fin 4 → ℝ := fun j => if j = i then (1 + 3 * s) / 4 else (1 - s) / 4

/-- The one-small spectrum with parameter `s`. -/
noncomputable def oneSmall (s : ℝ) (i : Fin 4) : Fin 4 → ℝ := fun j => if j = i then (1 - 3 * s) / 4 else (1 + s) / 4

/-! ### The cubic identity on centred vectors -/

theorem coord_bound {a b c d : ℝ} (h : a + b + c + d = 0) : 4 * a ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
  have h2 : (b + c + d) ^ 2 = a ^ 2 := by
    have : b + c + d = -a := by linarith
    rw [this]; ring
  nlinarith [h2, sq_nonneg (b - c), sq_nonneg (c - d), sq_nonneg (b - d)]

theorem coord_le {a b c d r : ℝ} (hr : 0 ≤ r) (h : a + b + c + d = 0)
    (hq : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 3 * r ^ 2) : a ≤ 3 * r / 2 ∧ -(3 * r / 2) ≤ a := by
  have := coord_bound h
  rw [hq] at this
  constructor <;> nlinarith [sq_nonneg (a - 3 * r / 2), sq_nonneg (a + 3 * r / 2)]

theorem g_identity {a b c d r : ℝ} (h : a + b + c + d = 0)
    (hq : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 3 * r ^ 2) :
    (a + r / 2) ^ 2 * (3 * r / 2 - a) + (b + r / 2) ^ 2 * (3 * r / 2 - b)
      + (c + r / 2) ^ 2 * (3 * r / 2 - c) + (d + r / 2) ^ 2 * (3 * r / 2 - d)
      = 3 * r ^ 3 - (a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3) := by
  have hd : d = -(a + b + c) := by linarith
  subst hd
  have : r ^ 2 = (a ^ 2 + b ^ 2 + c ^ 2 + (-(a + b + c)) ^ 2) / 3 := by linarith
  linear_combination (r / 2) * hq

theorem four_pattern {a b c d r : ℝ} (hr : 0 < r) (hsum : a + b + c + d = 0)
    (ha : a = -r / 2 ∨ a = 3 * r / 2) (hb : b = -r / 2 ∨ b = 3 * r / 2)
    (hc : c = -r / 2 ∨ c = 3 * r / 2) (hd : d = -r / 2 ∨ d = 3 * r / 2) :
    (a = 3 * r / 2 ∧ b = -r / 2 ∧ c = -r / 2 ∧ d = -r / 2) ∨
    (b = 3 * r / 2 ∧ a = -r / 2 ∧ c = -r / 2 ∧ d = -r / 2) ∨
    (c = 3 * r / 2 ∧ a = -r / 2 ∧ b = -r / 2 ∧ d = -r / 2) ∨
    (d = 3 * r / 2 ∧ a = -r / 2 ∧ b = -r / 2 ∧ c = -r / 2) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
    rcases hd with rfl | rfl <;> first | (exfalso; linarith) | simp

/-- Upper extremal value of `a³+b³+c³+d³` on `a+b+c+d = 0`, `a²+b²+c²+d² = 3 r²`. -/
theorem centred_upper4 {a b c d r : ℝ} (hr : 0 ≤ r) (hs : a + b + c + d = 0)
    (hq : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 3 * r ^ 2) :
    a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3 ≤ 3 * r ^ 3 ∧
      (a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3 = 3 * r ^ 3 ↔
        (a = 3 * r / 2 ∧ b = -r / 2 ∧ c = -r / 2 ∧ d = -r / 2) ∨
        (b = 3 * r / 2 ∧ a = -r / 2 ∧ c = -r / 2 ∧ d = -r / 2) ∨
        (c = 3 * r / 2 ∧ a = -r / 2 ∧ b = -r / 2 ∧ d = -r / 2) ∨
        (d = 3 * r / 2 ∧ a = -r / 2 ∧ b = -r / 2 ∧ c = -r / 2)) := by
  have ba := coord_le hr hs hq
  have bb := coord_le hr (by linarith : b + a + c + d = 0) (by linarith : b ^ 2 + a ^ 2 + c ^ 2 + d ^ 2 = 3 * r ^ 2)
  have bc := coord_le hr (by linarith : c + a + b + d = 0) (by linarith : c ^ 2 + a ^ 2 + b ^ 2 + d ^ 2 = 3 * r ^ 2)
  have bd := coord_le hr (by linarith : d + a + b + c = 0) (by linarith : d ^ 2 + a ^ 2 + b ^ 2 + c ^ 2 = 3 * r ^ 2)
  have hid := g_identity hs hq
  have ga : 0 ≤ (a + r / 2) ^ 2 * (3 * r / 2 - a) := mul_nonneg (sq_nonneg _) (by linarith [ba.1])
  have gb : 0 ≤ (b + r / 2) ^ 2 * (3 * r / 2 - b) := mul_nonneg (sq_nonneg _) (by linarith [bb.1])
  have gc : 0 ≤ (c + r / 2) ^ 2 * (3 * r / 2 - c) := mul_nonneg (sq_nonneg _) (by linarith [bc.1])
  have gd : 0 ≤ (d + r / 2) ^ 2 * (3 * r / 2 - d) := mul_nonneg (sq_nonneg _) (by linarith [bd.1])
  refine ⟨by linarith, ?_⟩
  constructor
  · intro h
    have z : ∀ t : ℝ, 0 ≤ (t + r / 2) ^ 2 * (3 * r / 2 - t) → (t + r / 2) ^ 2 * (3 * r / 2 - t) = 0 →
        t = -r / 2 ∨ t = 3 * r / 2 := by
      intro t _ h0
      rcases mul_eq_zero.1 h0 with h1 | h1
      · left; have := pow_eq_zero_iff (two_ne_zero) |>.1 h1; linarith
      · right; linarith
    have za := z a ga (by linarith)
    have zb := z b gb (by linarith)
    have zc := z c gc (by linarith)
    have zd := z d gd (by linarith)
    rcases hr.eq_or_lt with h0 | hpos
    · subst h0
      have : a = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg d]
      have : b = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg d]
      have : c = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg d]
      have : d = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg d]
      left; refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
    · exact four_pattern hpos hs za zb zc zd
  · rintro (⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩) <;>
      rw [h0, h1, h2, h3] <;> ring

/-- Lower extremal value, by the symmetry `w ↦ -w`. -/
theorem centred_lower4 {a b c d r : ℝ} (hr : 0 ≤ r) (hs : a + b + c + d = 0)
    (hq : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 3 * r ^ 2) :
    -(3 * r ^ 3) ≤ a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3 ∧
      (a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3 = -(3 * r ^ 3) ↔
        (a = -(3 * r / 2) ∧ b = r / 2 ∧ c = r / 2 ∧ d = r / 2) ∨
        (b = -(3 * r / 2) ∧ a = r / 2 ∧ c = r / 2 ∧ d = r / 2) ∨
        (c = -(3 * r / 2) ∧ a = r / 2 ∧ b = r / 2 ∧ d = r / 2) ∨
        (d = -(3 * r / 2) ∧ a = r / 2 ∧ b = r / 2 ∧ c = r / 2)) := by
  obtain ⟨h1, h2⟩ := centred_upper4 (a := -a) (b := -b) (c := -c) (d := -d) hr (by linarith)
    (by linarith)
  refine ⟨by nlinarith, ?_⟩
  have e : (-a) ^ 3 + (-b) ^ 3 + (-c) ^ 3 + (-d) ^ 3 = -(a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3) := by ring
  rw [e] at h2
  have e2 : (-(a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3) = 3 * r ^ 3) ↔
      (a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3 = -(3 * r ^ 3)) := by constructor <;> intro h <;> linarith
  rw [e2] at h2
  rw [h2]
  constructor <;> rintro (⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩)
  all_goals first
    | (left; refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith)
    | (right; left; refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith)
    | (right; right; left; refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith)
    | (right; right; right; refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith)


theorem pattern4_iff (l : Fin 4 → ℝ) (u v : ℝ) :
    (∃ i, l i = u ∧ ∀ j, j ≠ i → l j = v) ↔
      (l 0 = u ∧ l 1 = v ∧ l 2 = v ∧ l 3 = v) ∨ (l 1 = u ∧ l 0 = v ∧ l 2 = v ∧ l 3 = v) ∨
      (l 2 = u ∧ l 0 = v ∧ l 1 = v ∧ l 3 = v) ∨ (l 3 = u ∧ l 0 = v ∧ l 1 = v ∧ l 2 = v) := by
  constructor
  · rintro ⟨i, hi, hj⟩
    fin_cases i
    · left; exact ⟨hi, hj 1 (by decide), hj 2 (by decide), hj 3 (by decide)⟩
    · right; left; exact ⟨hi, hj 0 (by decide), hj 2 (by decide), hj 3 (by decide)⟩
    · right; right; left; exact ⟨hi, hj 0 (by decide), hj 1 (by decide), hj 3 (by decide)⟩
    · right; right; right; exact ⟨hi, hj 0 (by decide), hj 1 (by decide), hj 2 (by decide)⟩
  · rintro (⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩)
    · refine ⟨0, h0, ?_⟩; intro j hj; fin_cases j <;> simp_all
    · refine ⟨1, h0, ?_⟩; intro j hj; fin_cases j <;> simp_all
    · refine ⟨2, h0, ?_⟩; intro j hj; fin_cases j <;> simp_all
    · refine ⟨3, h0, ?_⟩; intro j hj; fin_cases j <;> simp_all

theorem shift_pattern (l : Fin 4 → ℝ) {u v u' v' : ℝ} (hu : u' = u + 1 / 4) (hv : v' = v + 1 / 4) :
    (∃ i, l i - 1 / 4 = u ∧ ∀ j, j ≠ i → l j - 1 / 4 = v) ↔
      ∃ i, l i = u' ∧ ∀ j, j ≠ i → l j = v' := by
  subst hu; subst hv
  constructor
  · rintro ⟨i, h1, h2⟩
    exact ⟨i, by linarith, fun j hj => by linarith [h2 j hj]⟩
  · rintro ⟨i, h1, h2⟩
    exact ⟨i, by linarith, fun j hj => by linarith [h2 j hj]⟩

/-- The pattern of the equality cases in terms of the four coordinates, centred at `1/4`. -/
theorem pattern4_centred (l : Fin 4 → ℝ) (u v : ℝ) :
    ((l 0 - 1 / 4 = u ∧ l 1 - 1 / 4 = v ∧ l 2 - 1 / 4 = v ∧ l 3 - 1 / 4 = v) ∨
      (l 1 - 1 / 4 = u ∧ l 0 - 1 / 4 = v ∧ l 2 - 1 / 4 = v ∧ l 3 - 1 / 4 = v) ∨
      (l 2 - 1 / 4 = u ∧ l 0 - 1 / 4 = v ∧ l 1 - 1 / 4 = v ∧ l 3 - 1 / 4 = v) ∨
      (l 3 - 1 / 4 = u ∧ l 0 - 1 / 4 = v ∧ l 1 - 1 / 4 = v ∧ l 2 - 1 / 4 = v)) ↔
    ∃ i, l i = u + 1 / 4 ∧ ∀ j, j ≠ i → l j = v + 1 / 4 := by
  rw [← shift_pattern l rfl rfl]
  exact (pattern4_iff (fun k => l k - 1 / 4) u v).symm

theorem rpow_three_halves_div {x r : ℝ} (hr : 0 ≤ r) (hx : x = 3 * r ^ 2) :
    x ^ (3 / 2 : ℝ) / Real.sqrt 3 = 3 * r ^ 3 := by
  have h3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have e1 : x ^ (3 / 2 : ℝ) = x * Real.sqrt x := by
    have hx0 : 0 ≤ x := by rw [hx]; positivity
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add' hx0 (by norm_num), Real.rpow_one,
      ← Real.sqrt_eq_rpow]
  have e2 : Real.sqrt x = Real.sqrt 3 * r := by
    rw [hx, Real.sqrt_mul (by norm_num), Real.sqrt_sq hr]
  rw [e1, e2, hx]
  field_simp

/-- **Sharp third-moment bound at fixed purity** (`lem:fqe-third-moment`).
For a four-point probability vector with purity `1/4 + x`: `0 ≤ x ≤ 3/4`,
`|t - 1/16 - 3x/4| ≤ x^{3/2}/√3`, the upper bound being attained exactly at the one-large spectrum
and the lower bound exactly at the one-small spectrum (`s = √(4x/3)`). -/
theorem third_moment (l : Fin 4 → ℝ) (hl : ∀ i, 0 ≤ l i) (hs : ∑ i, l i = 1) {x : ℝ}
    (hx : ∑ i, l i ^ 2 = 1 / 4 + x) :
    (0 ≤ x ∧ x ≤ 3 / 4) ∧
    |∑ i, l i ^ 3 - 1 / 16 - 3 * x / 4| ≤ x ^ (3 / 2 : ℝ) / Real.sqrt 3 ∧
    (∑ i, l i ^ 3 - 1 / 16 - 3 * x / 4 = x ^ (3 / 2 : ℝ) / Real.sqrt 3 ↔
      ∃ i, l i = (1 + 3 * Real.sqrt (4 * x / 3)) / 4 ∧
        ∀ j, j ≠ i → l j = (1 - Real.sqrt (4 * x / 3)) / 4) ∧
    (∑ i, l i ^ 3 - 1 / 16 - 3 * x / 4 = -(x ^ (3 / 2 : ℝ) / Real.sqrt 3) ↔
      ∃ i, l i = (1 - 3 * Real.sqrt (4 * x / 3)) / 4 ∧
        ∀ j, j ≠ i → l j = (1 + Real.sqrt (4 * x / 3)) / 4) := by
  simp only [Fin.sum_univ_four] at hs hx ⊢
  have hle : ∀ i, l i ≤ 1 := by
    intro i
    have := hl 0; have := hl 1; have := hl 2; have := hl 3
    fin_cases i <;> simp <;> linarith
  have hxs : x = (l 0 - 1 / 4) ^ 2 + (l 1 - 1 / 4) ^ 2 + (l 2 - 1 / 4) ^ 2 + (l 3 - 1 / 4) ^ 2 := by
    linear_combination (-1 : ℝ) * hx + (1 / 2) * hs
  have hx0 : 0 ≤ x := by rw [hxs]; positivity
  have hx1 : x ≤ 3 / 4 := by
    have k : ∀ i, l i ^ 2 ≤ l i := fun i => by nlinarith [hl i, hle i]
    have := k 0; have := k 1; have := k 2; have := k 3
    linarith
  set r : ℝ := Real.sqrt (x / 3) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : x = 3 * r ^ 2 := by rw [hr, Real.sq_sqrt (by positivity)]; ring
  have hsq : Real.sqrt (4 * x / 3) = 2 * r := by
    rw [show 4 * x / 3 = (2 * r) ^ 2 by rw [hr2]; ring, Real.sqrt_sq (by positivity)]
  rw [hsq]
  have hb := rpow_three_halves_div hr0 hr2
  rw [hb]
  have hsum : (l 0 - 1 / 4) + (l 1 - 1 / 4) + (l 2 - 1 / 4) + (l 3 - 1 / 4) = 0 := by linarith
  have hqd : (l 0 - 1 / 4) ^ 2 + (l 1 - 1 / 4) ^ 2 + (l 2 - 1 / 4) ^ 2 + (l 3 - 1 / 4) ^ 2
      = 3 * r ^ 2 := by rw [← hxs]; exact hr2
  have hcub : l 0 ^ 3 + l 1 ^ 3 + l 2 ^ 3 + l 3 ^ 3 - 1 / 16 - 3 * x / 4
      = (l 0 - 1 / 4) ^ 3 + (l 1 - 1 / 4) ^ 3 + (l 2 - 1 / 4) ^ 3 + (l 3 - 1 / 4) ^ 3 := by
    linear_combination (3 / 4) * hx - (3 / 16) * hs
  rw [hcub]
  obtain ⟨up, upiff⟩ := centred_upper4 hr0 hsum hqd
  obtain ⟨lo, loiff⟩ := centred_lower4 hr0 hsum hqd
  refine ⟨⟨hx0, hx1⟩, abs_le.2 ⟨by linarith, by linarith⟩, ?_, ?_⟩
  · rw [upiff, pattern4_centred]
    constructor <;> rintro ⟨i, h1, h2⟩ <;> exact ⟨i, by linarith, fun j hj => by linarith [h2 j hj]⟩
  · rw [loiff]
    have := pattern4_centred l (-(3 * r / 2)) (r / 2)
    rw [this]
    constructor <;> rintro ⟨i, h1, h2⟩ <;> exact ⟨i, by linarith, fun j hj => by linarith [h2 j hj]⟩

/-- The lower bound can be attained only when `x ≤ 1/12` (the one-small spectrum has a
nonnegative smallest entry exactly then). -/
theorem third_moment_lower_x_le (l : Fin 4 → ℝ) (hl : ∀ i, 0 ≤ l i) (hs : ∑ i, l i = 1) {x : ℝ}
    (hx : ∑ i, l i ^ 2 = 1 / 4 + x)
    (heq : ∑ i, l i ^ 3 - 1 / 16 - 3 * x / 4 = -(x ^ (3 / 2 : ℝ) / Real.sqrt 3)) : x ≤ 1 / 12 := by
  obtain ⟨⟨hx0, -⟩, -, -, h4⟩ := third_moment l hl hs hx
  obtain ⟨i, hi, -⟩ := h4.1 heq
  have h0 := hl i
  rw [hi] at h0
  have hsq : Real.sqrt (4 * x / 3) ≤ 1 / 3 := by linarith
  have h2 : 4 * x / 3 ≤ (1 / 3) ^ 2 := (Real.sqrt_le_left (by norm_num)).1 hsq
  linarith

theorem oneLarge_isProb {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 3 / 4) :
    let s := Real.sqrt (4 * x / 3)
    (∀ i, 0 ≤ oneLarge s 0 i) ∧ ∑ i, oneLarge s 0 i = 1 ∧ ∑ i, oneLarge s 0 i ^ 2 = 1 / 4 + x := by
  intro s
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = 4 * x / 3 := Real.sq_sqrt (by positivity)
  have hs1 : s ≤ 1 := by nlinarith
  refine ⟨?_, ?_, ?_⟩
  · intro i; unfold oneLarge; split_ifs <;> linarith
  · simp [oneLarge, Fin.sum_univ_four]; ring
  · simp [oneLarge, Fin.sum_univ_four]; nlinarith

theorem oneSmall_isProb {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 12) :
    let s := Real.sqrt (4 * x / 3)
    (∀ i, 0 ≤ oneSmall s 0 i) ∧ ∑ i, oneSmall s 0 i = 1 ∧ ∑ i, oneSmall s 0 i ^ 2 = 1 / 4 + x := by
  intro s
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = 4 * x / 3 := Real.sq_sqrt (by positivity)
  have hs1 : s ≤ 1 / 3 := by nlinarith
  refine ⟨?_, ?_, ?_⟩
  · intro i; unfold oneSmall; split_ifs <;> linarith
  · simp [oneSmall, Fin.sum_univ_four]; ring
  · simp [oneSmall, Fin.sum_univ_four]; nlinarith

/-- The upper bound is attained at every purity `1/4 + x`, `0 ≤ x ≤ 3/4`. -/
theorem third_moment_upper_attained {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 3 / 4) :
    ∃ l : Fin 4 → ℝ, (∀ i, 0 ≤ l i) ∧ ∑ i, l i = 1 ∧ ∑ i, l i ^ 2 = 1 / 4 + x ∧
      ∑ i, l i ^ 3 - 1 / 16 - 3 * x / 4 = x ^ (3 / 2 : ℝ) / Real.sqrt 3 := by
  obtain ⟨h1, h2, h3⟩ := oneLarge_isProb hx0 hx1
  refine ⟨oneLarge (Real.sqrt (4 * x / 3)) 0, h1, h2, h3, ?_⟩
  obtain ⟨-, -, h, -⟩ := third_moment _ h1 h2 h3
  exact h.2 ⟨0, by simp [oneLarge], fun j hj => by simp [oneLarge, hj]⟩

/-- The lower bound is attained at every purity `1/4 + x`, `0 ≤ x ≤ 1/12`. -/
theorem third_moment_lower_attained {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 12) :
    ∃ l : Fin 4 → ℝ, (∀ i, 0 ≤ l i) ∧ ∑ i, l i = 1 ∧ ∑ i, l i ^ 2 = 1 / 4 + x ∧
      ∑ i, l i ^ 3 - 1 / 16 - 3 * x / 4 = -(x ^ (3 / 2 : ℝ) / Real.sqrt 3) := by
  obtain ⟨h1, h2, h3⟩ := oneSmall_isProb hx0 hx1
  refine ⟨oneSmall (Real.sqrt (4 * x / 3)) 0, h1, h2, h3, ?_⟩
  obtain ⟨-, -, -, h⟩ := third_moment _ h1 h2 h3
  exact h.2 ⟨0, by simp [oneSmall], fun j hj => by simp [oneSmall, hj]⟩

/-- info: 'FormalResearch.FourQubitEntropy.third_moment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms third_moment

/-- info: 'FormalResearch.FourQubitEntropy.third_moment_lower_x_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms third_moment_lower_x_le

/-- info: 'FormalResearch.FourQubitEntropy.third_moment_upper_attained' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms third_moment_upper_attained

/-- info: 'FormalResearch.FourQubitEntropy.third_moment_lower_attained' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms third_moment_lower_attained

end FormalResearch.FourQubitEntropy
