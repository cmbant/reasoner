module

public import Mathlib
public import FormalResearch.Special.HermiteKappaOde
public import FormalResearch.Special.HermiteBulkProfile

/-!
# The Hermite functions at the origin

Exact values of `φ_n(0)` (the recurrence at `x = 0` gives `φ_{n+2}(0)² = ((n+1)/(n+2)) φ_n(0)²`,
`φ_1(0) = 0`, alternating signs) and their size to relative order `1/(n+1)` from the Wallis
product bounds of Mathlib (`Real.Wallis.le_W`, `Real.Wallis.W_le`):
`√(4m+1) φ_{2m}(0)² = 2/π + O(1/(2m+1))` and
`(2(2m+1)/√(4m+3)) φ_{2m}(0)² = 2/π + O(1/(2m+2))`.
These are the initial values of the Liouville-Green march of `hbk_rot`; they fix the amplitude
`√(2/π)` and, through parity and the sign alternation, the phase offset `-π/4` of the bulk
Plancherel-Rotach formula.
-/

@[expose] public section

open Real

namespace FormalResearch.Special

lemma hbk_phi_rec_zero (n : ℕ) :
    √(((n : ℝ) + 2) / 2) * hermitePhi (n + 2) 0 = -(√(((n : ℝ) + 1) / 2) * hermitePhi n 0) := by
  have h := hermitePsi_rec ((n : ℤ) + 1) (by omega) 0
  have e1 : hermitePsi ((n : ℤ) + 1 + 1) 0 = hermitePhi (n + 2) 0 := by
    have := hermitePsi_natCast (n + 2) 0; push_cast at this; rw [← this]; ring_nf
  have e2 : hermitePsi ((n : ℤ) + 1 - 1) 0 = hermitePhi n 0 := by
    have := hermitePsi_natCast n 0; simpa using this
  rw [e1, e2] at h
  push_cast at h
  have : √(((n : ℝ) + 1 + 1) / 2) = √(((n : ℝ) + 2) / 2) := by congr 1; ring
  rw [this] at h
  linarith

lemma hbk_phi_sq_rec_zero (n : ℕ) :
    hermitePhi (n + 2) 0 ^ 2 = ((n : ℝ) + 1) / ((n : ℝ) + 2) * hermitePhi n 0 ^ 2 := by
  have h := congrArg (fun t => t ^ 2) (hbk_phi_rec_zero n)
  simp only [neg_sq, mul_pow] at h
  rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)] at h
  have : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  field_simp at h ⊢
  linarith

lemma hbk_phi_one_zero : hermitePhi 1 0 = 0 := by
  rw [hermitePhi_one]; simp

lemma hbk_phi_odd_zero (m : ℕ) : hermitePhi (2 * m + 1) 0 = 0 := by
  induction m with
  | zero => simpa using hbk_phi_one_zero
  | succ m ih =>
    have h := hbk_phi_sq_rec_zero (2 * m + 1)
    have : 2 * (m + 1) + 1 = 2 * m + 1 + 2 := by ring
    rw [this]
    have h2 : hermitePhi (2 * m + 1 + 2) 0 ^ 2 = 0 := by rw [h, ih]; ring
    exact pow_eq_zero_iff (two_ne_zero) |>.1 h2

lemma hbk_phi_even_sign (m : ℕ) : 0 ≤ (-1 : ℝ) ^ m * hermitePhi (2 * m) 0 := by
  induction m with
  | zero =>
    simp [hermitePhi_zero]; positivity
  | succ m ih =>
    have h := hbk_phi_rec_zero (2 * m)
    have e : 2 * (m + 1) = 2 * m + 2 := by ring
    rw [e]
    have hp : 0 < √(((↑(2 * m) : ℝ) + 2) / 2) := Real.sqrt_pos.2 (by positivity)
    have : (-1 : ℝ) ^ (m + 1) * hermitePhi (2 * m + 2) 0 =
        (√(((↑(2 * m) : ℝ) + 1) / 2) / √(((↑(2 * m) : ℝ) + 2) / 2)) *
          ((-1) ^ m * hermitePhi (2 * m) 0) := by
      field_simp
      rw [pow_succ]
      linear_combination (-1 : ℝ) ^ m * (-1) * h
    rw [this]; positivity

lemma hbk_phi_zero_zero_sq : √π * hermitePhi 0 0 ^ 2 = 1 := by
  have h : hermitePhi 0 0 = π ^ (-(1 / 4 : ℝ)) := by simp [hermitePhi_zero]
  rw [h, ← Real.rpow_natCast, ← Real.rpow_mul Real.pi_pos.le, Real.sqrt_eq_rpow,
    ← Real.rpow_add Real.pi_pos]
  norm_num

/-- Wallis identity: `(2m+1) W_m (√π φ_{2m}(0)²)² = 1`. -/
lemma hbk_wallis_id (m : ℕ) :
    (2 * (m : ℝ) + 1) * Real.Wallis.W m * (√π * hermitePhi (2 * m) 0 ^ 2) ^ 2 = 1 := by
  induction m with
  | zero => simp [Real.Wallis.W, hbk_phi_zero_zero_sq]
  | succ m ih =>
    have h := hbk_phi_sq_rec_zero (2 * m)
    have e : 2 * (m + 1) = 2 * m + 2 := by ring
    rw [e, h, Real.Wallis.W_succ]
    push_cast
    have h1 : (0 : ℝ) < 2 * m + 1 := by positivity
    have h2 : (0 : ℝ) < 2 * m + 2 := by positivity
    have h3 : (0 : ℝ) < 2 * m + 3 := by positivity
    field_simp
    field_simp at ih
    linear_combination (2 * (m : ℝ) + 3) * ih

lemma hbk_abs_sub_one_le {z : ℝ} (hz : 0 ≤ z) : |z - 1| ≤ |z ^ 2 - 1| := by
  have : z ^ 2 - 1 = (z - 1) * (z + 1) := by ring
  rw [this, abs_mul]
  have : 1 ≤ |z + 1| := by rw [abs_of_nonneg (by linarith)]; linarith
  nlinarith [abs_nonneg (z - 1)]

/-- Core size lemma: if `z ≥ 0`, `z² · (4 a W) = c π` with `W ∈ [a/(a+1) π/2, π/2]`, then
`|z² - 1|` is controlled. -/
lemma hbk_core (z W a c : ℝ) (ha : 0 < a) (hW1 : a / (a + 1) * (π / 2) ≤ W)
    (hW2 : W ≤ π / 2) (h : z ^ 2 * (4 * a * W) = c * π) (hc : 0 < c) :
    c / (2 * a) ≤ z ^ 2 ∧ z ^ 2 ≤ c * (a + 1) / (2 * a ^ 2) := by
  have hpi := Real.pi_pos
  have hWp : 0 < W := lt_of_lt_of_le (by positivity) hW1
  constructor
  · by_contra hlt
    replace hlt := not_le.1 hlt
    have : z ^ 2 * (4 * a * W) < c / (2 * a) * (4 * a * W) :=
      mul_lt_mul_of_pos_right hlt (by positivity)
    have h2 : c / (2 * a) * (4 * a * W) = 2 * c * W := by field_simp; ring
    nlinarith
  · by_contra hlt
    replace hlt := not_le.1 hlt
    have : c * (a + 1) / (2 * a ^ 2) * (4 * a * W) < z ^ 2 * (4 * a * W) :=
      mul_lt_mul_of_pos_right hlt (by positivity)
    have h2 : c * (a + 1) / (2 * a ^ 2) * (4 * a * W) = 2 * c * (a + 1) / a * W := by
      field_simp; ring
    have h3 : 2 * c * (a + 1) / a * W ≥ 2 * c * (a + 1) / a * (a / (a + 1) * (π / 2)) :=
      mul_le_mul_of_nonneg_left hW1 (by positivity)
    have h4 : 2 * c * (a + 1) / a * (a / (a + 1) * (π / 2)) = c * π := by field_simp
    nlinarith

lemma hbk_W_bounds (m : ℕ) :
    (2 * (m : ℝ) + 1) / (2 * m + 1 + 1) * (π / 2) ≤ Real.Wallis.W m ∧
      Real.Wallis.W m ≤ π / 2 := by
  refine ⟨?_, Real.Wallis.W_le m⟩
  have := Real.Wallis.le_W m
  convert this using 2; ring

lemma hbk_q_wallis (m : ℕ) :
    (2 * (m : ℝ) + 1) * Real.Wallis.W m * π * (hermitePhi (2 * m) 0 ^ 2) ^ 2 = 1 := by
  have h := hbk_wallis_id m
  rw [mul_pow, Real.sq_sqrt Real.pi_pos.le] at h
  linear_combination h

/-- `|√(4m+1) φ_{2m}(0)² - 2/π| ≤ 1/(2m+1)`. -/
theorem hbk_even_size (m : ℕ) :
    |√(4 * (m : ℝ) + 1) * hermitePhi (2 * m) 0 ^ 2 - 2 / π| ≤ 1 / (2 * (m : ℝ) + 1) := by
  have hpi := Real.pi_pos
  have hid := hbk_q_wallis m
  obtain ⟨hW1, hW2⟩ := hbk_W_bounds m
  generalize hq : hermitePhi (2 * m) 0 ^ 2 = q at hid ⊢
  have hq0 : 0 ≤ q := by rw [← hq]; exact sq_nonneg _
  generalize hW : Real.Wallis.W m = W at hid hW1 hW2
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = 2 * m + 1 := ⟨_, rfl⟩
  rw [← ha] at hid hW1 ⊢
  have hW1' : a / (a + 1) * (π / 2) ≤ W := hW1
  have ha0 : 0 < a := by rw [ha]; positivity
  have hs : √(4 * (m : ℝ) + 1) ^ 2 = 4 * m + 1 := Real.sq_sqrt (by positivity)
  generalize hu : √(4 * (m : ℝ) + 1) * q = u
  have hu0 : 0 ≤ u := by rw [← hu]; positivity
  have hz0 : 0 ≤ π * u / 2 := by positivity
  have hz2 : (π * u / 2) ^ 2 * (4 * a * W) = (4 * m + 1) * π := by
    have : (π * u / 2) ^ 2 = π ^ 2 * ((4 * m + 1) * q ^ 2) / 4 := by
      rw [← hu, div_pow, mul_pow, mul_pow, hs]; ring
    rw [this]
    have key : π ^ 2 * ((4 * (m : ℝ) + 1) * q ^ 2) / 4 * (4 * a * W) =
        (4 * m + 1) * π * (a * W * π * q ^ 2) := by ring
    rw [key, hid, mul_one]
  have hc : (0 : ℝ) < 4 * m + 1 := by positivity
  obtain ⟨c1, c2⟩ := hbk_core (π * u / 2) W a (4 * m + 1) ha0 hW1' hW2 hz2 hc
  have e1 : (4 * (m : ℝ) + 1) / (2 * a) = 1 - 1 / (2 * a) := by rw [ha]; field_simp; ring
  have e2 : (4 * (m : ℝ) + 1) * (a + 1) / (2 * a ^ 2) = 1 + 1 / (2 * a) - 1 / (2 * a ^ 2) := by
    rw [ha]; field_simp; ring
  have e3 : 0 ≤ 1 / (2 * a ^ 2) := by positivity
  have h1 : |(π * u / 2) ^ 2 - 1| ≤ 1 / (2 * a) := by
    rw [abs_le]; constructor <;> linarith
  have h2 : |π * u / 2 - 1| ≤ 1 / (2 * a) := (hbk_abs_sub_one_le hz0).trans h1
  have h3 : u - 2 / π = 2 / π * (π * u / 2 - 1) := by field_simp
  rw [h3, abs_mul, abs_of_pos (by positivity)]
  have : 2 / π ≤ 1 := by rw [div_le_one hpi]; linarith [Real.pi_gt_three]
  calc 2 / π * |π * u / 2 - 1| ≤ 1 * (1 / (2 * a)) :=
        mul_le_mul this h2 (abs_nonneg _) (by norm_num)
    _ ≤ 1 / a := by rw [one_mul]; exact one_div_le_one_div_of_le ha0 (by linarith)

/-- `|(2(2m+1)/√(4m+3)) φ_{2m}(0)² - 2/π| ≤ 1/(2m+2)`. -/
theorem hbk_odd_size (m : ℕ) :
    |2 * (2 * (m : ℝ) + 1) / √(4 * (m : ℝ) + 3) * hermitePhi (2 * m) 0 ^ 2 - 2 / π| ≤
      1 / (2 * (m : ℝ) + 2) := by
  have hpi := Real.pi_pos
  have hid := hbk_q_wallis m
  obtain ⟨hW1, hW2⟩ := hbk_W_bounds m
  generalize hq : hermitePhi (2 * m) 0 ^ 2 = q at hid ⊢
  have hq0 : 0 ≤ q := by rw [← hq]; exact sq_nonneg _
  generalize hW : Real.Wallis.W m = W at hid hW1 hW2
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = 2 * m + 1 := ⟨_, rfl⟩
  rw [← ha] at hid hW1 ⊢
  have hW1' : a / (a + 1) * (π / 2) ≤ W := hW1
  have ha0 : 0 < a := by rw [ha]; positivity
  have hs : √(4 * (m : ℝ) + 3) ^ 2 = 4 * m + 3 := Real.sq_sqrt (by positivity)
  have h2a : 2 * a + 1 = 4 * m + 3 := by rw [ha]; ring
  generalize hv : 2 * a / √(4 * (m : ℝ) + 3) * q = v
  have hv0 : 0 ≤ v := by rw [← hv]; positivity
  have hz0 : 0 ≤ π * v / 2 := by positivity
  have hz2 : (π * v / 2) ^ 2 * (4 * a * W) = (4 * a ^ 2 / (2 * a + 1)) * π := by
    have : (π * v / 2) ^ 2 = π ^ 2 * (a ^ 2 * q ^ 2 / (2 * a + 1)) := by
      rw [← hv, div_pow, mul_pow, mul_pow, div_pow, mul_pow, hs, ← h2a]; ring
    rw [this]
    have h3 : (2 * a + 1) ≠ 0 := by positivity
    have key : π ^ 2 * (a ^ 2 * q ^ 2 / (2 * a + 1)) * (4 * a * W) =
        (4 * a ^ 2 / (2 * a + 1)) * π * (a * W * π * q ^ 2) := by field_simp
    rw [key, hid, mul_one]
  have hc : (0 : ℝ) < 4 * a ^ 2 / (2 * a + 1) := by positivity
  obtain ⟨c1, c2⟩ := hbk_core (π * v / 2) W a _ ha0 hW1' hW2 hz2 hc
  have e1 : 4 * a ^ 2 / (2 * a + 1) / (2 * a) = 1 - 1 / (2 * a + 1) := by
    field_simp; ring
  have e2 : 4 * a ^ 2 / (2 * a + 1) * (a + 1) / (2 * a ^ 2) = 1 + 1 / (2 * a + 1) := by
    field_simp; ring
  have h1 : |(π * v / 2) ^ 2 - 1| ≤ 1 / (2 * a + 1) := by
    rw [abs_le]; constructor <;> linarith
  have h2 : |π * v / 2 - 1| ≤ 1 / (2 * a + 1) := (hbk_abs_sub_one_le hz0).trans h1
  have h3 : v - 2 / π = 2 / π * (π * v / 2 - 1) := by field_simp
  rw [h3, abs_mul, abs_of_pos (by positivity)]
  have : 2 / π ≤ 1 := by rw [div_le_one hpi]; linarith [Real.pi_gt_three]
  have hrw : (2 : ℝ) * m + 2 = a + 1 := by rw [ha]; ring
  rw [hrw]
  calc 2 / π * |π * v / 2 - 1| ≤ 1 * (1 / (2 * a + 1)) :=
        mul_le_mul this h2 (abs_nonneg _) (by norm_num)
    _ ≤ 1 / (a + 1) := by rw [one_mul]; exact one_div_le_one_div_of_le (by linarith) (by linarith)

lemma hbk_E0_sq {L : ℝ} (hL : 0 < L) : hbk_E L 0 ^ 2 = √L := by
  rw [hbk_E_sq (by simpa using hL)]; simp [hbk_w]

lemma hbk_hkDer_zero_even (m : ℕ) : hkDer (2 * m) 0 = 0 := by
  unfold hkDer
  have h1 : hermitePsi (((2 * m : ℕ) : ℤ) + 1) 0 = 0 := by
    have := hermitePsi_natCast (2 * m + 1) 0
    push_cast at this ⊢; rw [this]; exact hbk_phi_odd_zero m
  have h2 : hermitePsi (((2 * m : ℕ) : ℤ) - 1) 0 = 0 := by
    rcases m with _ | m
    · exact hermitePsi_neg (by simp) 0
    · have := hermitePsi_natCast (2 * m + 1) 0
      have e : (((2 * (m + 1) : ℕ) : ℤ) - 1) = ((2 * m + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [e, this]; exact hbk_phi_odd_zero m
  rw [h1, h2]; simp

lemma hbk_hkDer_zero_odd (m : ℕ) :
    hkDer (2 * m + 1) 0 = 2 * √(((2 * m + 1 : ℕ) : ℝ) / 2) * hermitePhi (2 * m) 0 := by
  unfold hkDer
  have h1 : hermitePsi (((2 * m + 1 : ℕ) : ℤ) + 1) 0 = hermitePhi (2 * m + 2) 0 := by
    have := hermitePsi_natCast (2 * m + 2) 0
    push_cast at this ⊢; rw [← this]; ring_nf
  have h2 : hermitePsi (((2 * m + 1 : ℕ) : ℤ) - 1) 0 = hermitePhi (2 * m) 0 := by
    have := hermitePsi_natCast (2 * m) 0
    push_cast at this ⊢; rw [← this]; ring_nf
  rw [h1, h2]
  have h := hbk_phi_rec_zero (2 * m)
  have e : √((((2 * m + 1 : ℕ) : ℝ) + 1) / 2) = √(((((2 * m : ℕ) : ℝ)) + 2) / 2) := by
    congr 1; push_cast; ring
  have e2 : √((((2 * m : ℕ) : ℝ) + 1) / 2) = √(((2 * m + 1 : ℕ) : ℝ) / 2) := by
    congr 1; push_cast; ring
  rw [e]
  rw [e2] at h
  linear_combination (-1 : ℝ) * h

/-- **Initial values of the Liouville-Green march.**  With `L = 2n+1`,
`U₀ = hbk_U L φ_n 0`, `V₀ = hbk_V L φ_n φ_n' 0`: there is `c ≥ 0` with `c² = U₀² + V₀²`,
`|c² - 2/π| ≤ 1/(n+1)`, and, for every `Φ`,
`U₀ cos(nπ/2 - Φ) + V₀ sin(nπ/2 - Φ) = c cos Φ`.  (Parity: `V₀ = 0` for even `n`, `U₀ = 0`
for odd `n`; the sign `(-1)^{⌊n/2⌋}` of `φ_n(0)`, resp. `φ_n'(0)`, produces the phase.) -/
theorem hbk_origin (n : ℕ) : ∃ c : ℝ, 0 ≤ c ∧
    c ^ 2 = hbk_U (2 * (n : ℝ) + 1) (hermitePhi n) 0 ^ 2 +
      hbk_V (2 * (n : ℝ) + 1) (hermitePhi n) (hkDer n) 0 ^ 2 ∧
    |c ^ 2 - 2 / π| ≤ 1 / ((n : ℝ) + 1) ∧
    ∀ Φ : ℝ, hbk_U (2 * (n : ℝ) + 1) (hermitePhi n) 0 * cos (n * π / 2 - Φ) +
      hbk_V (2 * (n : ℝ) + 1) (hermitePhi n) (hkDer n) 0 * sin (n * π / 2 - Φ) = c * cos Φ := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · -- even
    have hL : 2 * ((2 * m : ℕ) : ℝ) + 1 = 4 * m + 1 := by push_cast; ring
    rw [hL]
    have hE := hbk_E0_sq (L := 4 * (m : ℝ) + 1) (by positivity)
    have hEp : 0 < hbk_E (4 * (m : ℝ) + 1) 0 := hbk_E_pos (by simp; positivity)
    have hV : hbk_V (4 * (m : ℝ) + 1) (hermitePhi (2 * m)) (hkDer (2 * m)) 0 = 0 := by
      simp [hbk_V, hbk_hkDer_zero_even]
    have hU : hbk_U (4 * (m : ℝ) + 1) (hermitePhi (2 * m)) 0 =
        hbk_E (4 * (m : ℝ) + 1) 0 * hermitePhi (2 * m) 0 := rfl
    refine ⟨hbk_E (4 * (m : ℝ) + 1) 0 * |hermitePhi (2 * m) 0|, by positivity, ?_, ?_, ?_⟩
    · rw [hV, hU, mul_pow, mul_pow, sq_abs]; ring
    · have h := hbk_even_size m
      have : (hbk_E (4 * (m : ℝ) + 1) 0 * |hermitePhi (2 * m) 0|) ^ 2 =
          √(4 * (m : ℝ) + 1) * hermitePhi (2 * m) 0 ^ 2 := by
        rw [mul_pow, sq_abs, hE]
      rw [this]
      convert h using 2
      push_cast; ring
    · intro Φ
      rw [hV, hU, zero_mul, add_zero]
      have hc : cos (((2 * m : ℕ) : ℝ) * π / 2 - Φ) = (-1) ^ m * cos Φ := by
        have : ((2 * m : ℕ) : ℝ) * π / 2 - Φ = m * π - Φ := by push_cast; ring
        rw [this, cos_sub, cos_nat_mul_pi, sin_nat_mul_pi]; ring
      rw [hc]
      have hs := hbk_phi_even_sign m
      have habs : |hermitePhi (2 * m) 0| = (-1) ^ m * hermitePhi (2 * m) 0 := by
        rw [← abs_of_nonneg hs, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      rw [habs]
      ring
  · -- odd
    have hL : 2 * ((2 * m + 1 : ℕ) : ℝ) + 1 = 4 * m + 3 := by push_cast; ring
    rw [hL]
    have hE := hbk_E0_sq (L := 4 * (m : ℝ) + 3) (by positivity)
    have hEp : 0 < hbk_E (4 * (m : ℝ) + 3) 0 := hbk_E_pos (by simp; positivity)
    have hU : hbk_U (4 * (m : ℝ) + 3) (hermitePhi (2 * m + 1)) 0 = 0 := by
      simp [hbk_U, hbk_phi_odd_zero]
    have hV : hbk_V (4 * (m : ℝ) + 3) (hermitePhi (2 * m + 1)) (hkDer (2 * m + 1)) 0 =
        2 * √(((2 * m + 1 : ℕ) : ℝ) / 2) * hermitePhi (2 * m) 0 / hbk_E (4 * (m : ℝ) + 3) 0 := by
      simp [hbk_V, hbk_hkDer_zero_odd]
    have hs := hbk_phi_even_sign m
    set r := √(((2 * m + 1 : ℕ) : ℝ) / 2) with hr
    have hr0 : 0 ≤ r := Real.sqrt_nonneg _
    have hr2 : r ^ 2 = ((2 * m + 1 : ℕ) : ℝ) / 2 := Real.sq_sqrt (by positivity)
    refine ⟨2 * r * |hermitePhi (2 * m) 0| / hbk_E (4 * (m : ℝ) + 3) 0, by positivity, ?_, ?_, ?_⟩
    · rw [hU, hV]; simp only [div_pow, mul_pow, sq_abs]; ring
    · have h := hbk_odd_size m
      have : (2 * r * |hermitePhi (2 * m) 0| / hbk_E (4 * (m : ℝ) + 3) 0) ^ 2 =
          2 * (2 * (m : ℝ) + 1) / √(4 * (m : ℝ) + 3) * hermitePhi (2 * m) 0 ^ 2 := by
        rw [div_pow, mul_pow, mul_pow, sq_abs, hr2, hE]; push_cast; ring
      rw [this]
      convert h using 2
      push_cast; ring
    · intro Φ
      rw [hU, hV, zero_mul, zero_add]
      have hc : sin (((2 * m + 1 : ℕ) : ℝ) * π / 2 - Φ) = (-1) ^ m * cos Φ := by
        have : ((2 * m + 1 : ℕ) : ℝ) * π / 2 - Φ = (π / 2 - Φ) + m * π := by push_cast; ring
        rw [this, sin_add_nat_mul_pi, sin_pi_div_two_sub]
      rw [hc]
      have habs : |hermitePhi (2 * m) 0| = (-1) ^ m * hermitePhi (2 * m) 0 := by
        rw [← abs_of_nonneg hs, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      rw [habs]
      have : (-1 : ℝ) ^ m * (-1) ^ m = 1 := by rw [← mul_pow]; simp
      field_simp

end FormalResearch.Special

/-- info: 'FormalResearch.Special.hbk_origin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.hbk_origin
