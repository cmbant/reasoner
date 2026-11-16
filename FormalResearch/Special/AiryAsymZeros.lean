module

public import FormalResearch.Special.AiryAsymReal

/-!
# The zeros of `Ai` far on the negative axis (unlabelled)

From the explicit oscillatory asymptotics of `AiryAsymNeg` (`Ai(-r²) = cos φ/(√π √r) + O(r^{-7/2})`,
`Ai'(-r²) = √r sin φ/√π + O(r^{-5/2})`, `φ = (2/3) r³ - π/4`) one reads off, without Prüfer theory, the zeros of
`Ai` on `(-∞, -4]`: since `Ai(-r²)` has the sign of `cos φ` where `|cos φ| ≥ 1/2` and `Ai'(-r²) ≠ 0` where
`|sin φ| ≥ 1/2`,

* `airy_zero_location`: every zero `-y` of `Ai` with `y ≥ 4` satisfies
  `|(2/3) y^{3/2} - (k + 3/4) π| ≤ (2/5) y^{-3/2}` for some integer `k`
  (DLMF 9.9.6 with its first correction: `(2/3)|a_n|^{3/2} = (n - 1/4)π + O(n^{-1})`, `k = n - 1`);
* `airy_zero_window_existsUnique`: for every integer `k ≥ 2` there is exactly one `y > 0` with `Ai(-y) = 0`
  and `|(2/3) y^{3/2} - (k + 3/4) π| < π/3`.

Hence every zero in `(-∞, -4]` has an integer label `k` with `O(y^{-3/2})` location in the phase, and the
zeros with `k ≥ 2` are in bijection with the integers `k ≥ 2` (the zero with `k = 1`, `a_2 ≈ -4.088`, is not covered
by the uniqueness statement).  **Not proved here:** the labelling of these zeros against the ordered zeros
`a_1 > a_2 > ...` (that the `n`-th zero has `k = n - 1`; this needs the number of zeros in `[-4, 0]`, a finite
numerical input, or the Prüfer count of `AiryNodes`), the next term of DLMF 9.9.18 (`5/(48 t²)`), and
sharper constants.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.Special

lemma sqrtpi_lt_two : √π < 2 := by
  rw [Real.sqrt_lt' (by norm_num)]; nlinarith [Real.pi_lt_four]

/-- Where `|cos φ| ≥ 1/2`, `Ai(-r²)` has the sign of `cos φ` (`r ≥ 1`). -/
lemma airyAi_neg_sq_mul_cos_pos {r : ℝ} (hr : 1 ≤ r)
    (hc : 1 / 2 ≤ |Real.cos (2 / 3 * r ^ 3 - π / 4)|) :
    0 < airyAi (-(r ^ 2)) * Real.cos (2 / 3 * r ^ 3 - π / 4) := by
  have hr0 : 0 < r := by linarith
  have h := airyAi_neg_sq_asymptotic hr0
  set c := Real.cos (2 / 3 * r ^ 3 - π / 4) with hc0
  have hs : 0 < √r := Real.sqrt_pos.mpr hr0
  have hT : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
  have hM : 0 < √π * √r := by positivity
  have hc1 : |c| ≤ 1 := Real.abs_cos_le_one _
  have hsq : 1 / 4 ≤ c ^ 2 := by
    have := sq_abs c
    nlinarith [abs_nonneg c]
  have hr3 : 1 ≤ r ^ 3 := one_le_pow₀ hr
  have he : 1 / (8 * (√r * r ^ 3)) < 1 / (4 * (√π * √r)) := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sqrtpi_lt_two, mul_pos hs hs, mul_lt_mul_of_pos_right
      (show √π < 2 * r ^ 3 by linarith [sqrtpi_lt_two]) hs]
  set δ := airyAi (-(r ^ 2)) - c / (√π * √r) with hδ
  have hδc : |δ * c| ≤ 1 / (8 * (√r * r ^ 3)) := by
    rw [abs_mul]
    calc |δ| * |c| ≤ |δ| * 1 := mul_le_mul_of_nonneg_left hc1 (abs_nonneg _)
      _ ≤ _ := by rw [mul_one]; exact h
  have e : airyAi (-(r ^ 2)) * c = c ^ 2 / (√π * √r) + δ * c := by
    rw [hδ]; ring
  have h2 : 1 / (4 * (√π * √r)) ≤ c ^ 2 / (√π * √r) := by
    rw [show 1 / (4 * (√π * √r)) = (1 / 4) / (√π * √r) by field_simp]
    exact div_le_div_of_nonneg_right hsq hM.le
  have := (abs_le.mp hδc).1
  linarith

/-- Where `|sin φ| ≥ 1/2` (and `r ≥ 2`), `Ai'(-r²) ≠ 0`. -/
lemma airyAi'_neg_sq_ne_zero {r : ℝ} (hr : 2 ≤ r)
    (hs : 1 / 2 ≤ |Real.sin (2 / 3 * r ^ 3 - π / 4)|) : airyAi' (-(r ^ 2)) ≠ 0 := by
  have hr0 : 0 < r := by linarith
  have h := airyAi'_neg_sq_asymptotic hr0
  intro h0
  rw [h0, zero_sub, abs_neg] at h
  have hsr : 0 < √r := Real.sqrt_pos.mpr hr0
  have hT : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
  rw [abs_div, abs_mul, abs_of_pos hsr, abs_of_pos hT] at h
  have h1 : √r * (1 / 2) / √π ≤ √r * |Real.sin (2 / 3 * r ^ 3 - π / 4)| / √π :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hs hsr.le) hT.le
  have h2 := h1.trans h
  have hr3 : 8 ≤ r ^ 3 := by nlinarith [sq_nonneg r, mul_pos hr0 hr0]
  rw [div_le_div_iff₀ hT (by positivity)] at h2
  nlinarith [sqrtpi_lt_two, Real.mul_self_sqrt hr0.le, mul_pos hsr hsr, mul_pos hsr hT]

lemma hasDerivAt_airyAi_neg_sq (r : ℝ) :
    HasDerivAt (fun r : ℝ => airyAi (-(r ^ 2))) (airyAi' (-(r ^ 2)) * (-(2 * r))) r := by
  have h1 : HasDerivAt (fun r : ℝ => -(r ^ 2)) (-(2 * r)) r := by
    exact (hasDerivAt_pow 2 r).neg.congr_deriv (by simp)
  exact (hasDerivAt_airyAi (-(r ^ 2))).comp r h1

lemma continuous_airyAi_neg_sq : Continuous (fun r : ℝ => airyAi (-(r ^ 2))) :=
  continuous_iff_continuousAt.mpr fun r => (hasDerivAt_airyAi_neg_sq r).continuousAt

/-! ### Trigonometric facts -/

lemma abs_cos_shift (x : ℝ) (k : ℤ) : |Real.cos (x + (k + 1 / 2) * π)| = |Real.sin x| := by
  rw [show x + (k + 1 / 2) * π = (x + π / 2) + k * π by ring, Real.cos_add_int_mul_pi,
    Real.cos_add_pi_div_two, abs_mul, abs_neg_one_zpow, one_mul, abs_neg]

lemma abs_sin_shift (x : ℝ) (k : ℤ) : |Real.sin (x + (k + 1 / 2) * π)| = |Real.cos x| := by
  rw [show x + (k + 1 / 2) * π = (x + π / 2) + k * π by ring, Real.sin_add_int_mul_pi,
    Real.sin_add_pi_div_two, abs_mul, abs_neg_one_zpow, one_mul]

lemma half_le_abs_cos {x : ℝ} (hx : |x| ≤ π / 3) : 1 / 2 ≤ |Real.cos x| := by
  have h : Real.cos (π / 3) ≤ Real.cos |x| :=
    Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg x) (by linarith [Real.pi_pos]) hx
  rw [Real.cos_pi_div_three, Real.cos_abs] at h
  exact h.trans (le_abs_self _)

lemma cos_shift (x : ℝ) (k : ℤ) :
    Real.cos (x + (k + 1 / 2) * π) = (-1) ^ k * (-Real.sin x) := by
  rw [show x + (k + 1 / 2) * π = (x + π / 2) + k * π by ring, Real.cos_add_int_mul_pi,
    Real.cos_add_pi_div_two]

/-- Inside the window `|ξ - (k + 3/4)π| ≤ π/3`, `k ≥ 2`: `r > 2` and `|sin φ| ≥ 1/2`. -/
lemma window_facts {r : ℝ} {k : ℤ} (hk : 2 ≤ k) (hw : |2 / 3 * r ^ 3 - (k + 3 / 4) * π| ≤ π / 3) :
    2 ≤ r ∧ 1 / 2 ≤ |Real.sin (2 / 3 * r ^ 3 - π / 4)| := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hπ := Real.pi_gt_three
  have hw' := abs_le.mp hw
  constructor
  · by_contra hr
    push Not at hr
    have h1 : r ^ 3 < 2 ^ 3 := by
      rcases le_or_gt 0 r with h0 | h0
      · exact pow_lt_pow_left₀ hr h0 (by norm_num)
      · nlinarith [sq_nonneg r, mul_pos (neg_pos.mpr h0) (neg_pos.mpr h0)]
    nlinarith [mul_le_mul_of_nonneg_right hk' Real.pi_pos.le]
  · have e : 2 / 3 * r ^ 3 - π / 4 = (2 / 3 * r ^ 3 - (k + 3 / 4) * π) + (k + 1 / 2) * π := by ring
    rw [e, abs_sin_shift]
    exact half_le_abs_cos (abs_le.mpr hw')

lemma airyRoot_cube {t : ℝ} (ht : 0 ≤ t) : (((3 / 2) * t) ^ (1 / 3 : ℝ)) ^ 3 = (3 / 2) * t := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  norm_num

lemma airyRoot_pos {t : ℝ} (ht : 0 < t) : 0 < ((3 / 2) * t) ^ (1 / 3 : ℝ) :=
  Real.rpow_pos_of_pos (by positivity) _

lemma abs_sin_pi_div_three_eq {σ : ℝ} (hσ : |σ| = π / 3) : |Real.sin σ| = √3 / 2 := by
  rcases abs_eq (by positivity : 0 ≤ π / 3) |>.mp hσ with h | h
  · rw [h, Real.sin_pi_div_three, abs_of_pos (by positivity)]
  · rw [h, Real.sin_neg, abs_neg, Real.sin_pi_div_three, abs_of_pos (by positivity)]

/-- At an endpoint `ξ - π/4 = σ + (k + 1/2)π`, `|σ| = π/3`, of a window: `r ≥ 2` and
`Ai(-r²)` has the sign of `(-1)^k (-sin σ)`. -/
lemma window_endpoint {k : ℤ} (hk : 2 ≤ k) {r σ : ℝ} (hσ : |σ| = π / 3)
    (hx : 2 / 3 * r ^ 3 - π / 4 = σ + (k + 1 / 2) * π) :
    2 ≤ r ∧ 0 < airyAi (-(r ^ 2)) * ((-1) ^ k * (-Real.sin σ)) := by
  have hr2 : 2 ≤ r := by
    refine (window_facts hk ?_).1
    have : 2 / 3 * r ^ 3 - (k + 3 / 4) * π = σ := by linarith
    rw [this, hσ]
  refine ⟨hr2, ?_⟩
  have hc : Real.cos (2 / 3 * r ^ 3 - π / 4) = (-1) ^ k * (-Real.sin σ) := by
    rw [hx, cos_shift]
  have habs : |Real.cos (2 / 3 * r ^ 3 - π / 4)| = √3 / 2 := by
    rw [hx, abs_cos_shift, abs_sin_pi_div_three_eq hσ]
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hs3 : (0 : ℝ) < √3 := Real.sqrt_pos.mpr (by norm_num)
  have := airyAi_neg_sq_mul_cos_pos (r := r) (by linarith) (by rw [habs]; nlinarith)
  rwa [hc] at this

lemma airyRoot_data {t : ℝ} (ht : 0 < t) :
    ∃ a : ℝ, 0 < a ∧ 2 / 3 * a ^ 3 = t := by
  refine ⟨((3 / 2) * t) ^ (1 / 3 : ℝ), airyRoot_pos ht, ?_⟩
  rw [airyRoot_cube ht.le]; ring

/-- **Existence** of a zero in each window, `k ≥ 2`. -/
theorem airy_zero_window_exists {k : ℤ} (hk : 2 ≤ k) :
    ∃ r : ℝ, 0 < r ∧ |2 / 3 * r ^ 3 - (k + 3 / 4) * π| < π / 3 ∧ airyAi (-(r ^ 2)) = 0 := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hπ := Real.pi_gt_three
  have hc1 : 0 < (k + 3 / 4) * π - π / 3 := by nlinarith
  obtain ⟨a, ha0, ha3⟩ := airyRoot_data hc1
  obtain ⟨b, hb0, hb3⟩ := airyRoot_data (by linarith : 0 < (k + 3 / 4) * π + π / 3)
  have hab : a < b := by
    by_contra h
    push Not at h
    have := pow_le_pow_left₀ hb0.le h 3
    linarith [Real.pi_pos]
  have hxa : 2 / 3 * a ^ 3 - π / 4 = (-(π / 3)) + (k + 1 / 2) * π := by rw [ha3]; ring
  have hxb : 2 / 3 * b ^ 3 - π / 4 = (π / 3) + (k + 1 / 2) * π := by rw [hb3]; ring
  have hA := window_endpoint hk (σ := -(π / 3)) (by rw [abs_neg, abs_of_pos (by positivity)]) hxa
  have hB := window_endpoint hk (σ := π / 3) (by rw [abs_of_pos (by positivity)]) hxb
  rw [Real.sin_neg, neg_neg, Real.sin_pi_div_three] at hA
  rw [Real.sin_pi_div_three] at hB
  have hpp : ((-1 : ℝ) ^ k) * ((-1 : ℝ) ^ k) = 1 := by rw [← mul_zpow]; norm_num
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hprod : airyAi (-(a ^ 2)) * airyAi (-(b ^ 2)) < 0 := by
    by_contra hnn
    push Not at hnn
    have h1 := mul_pos hA.2 hB.2
    have e : (airyAi (-(a ^ 2)) * ((-1) ^ k * (√3 / 2))) *
        (airyAi (-(b ^ 2)) * ((-1) ^ k * (-(√3 / 2)))) =
        -(airyAi (-(a ^ 2)) * airyAi (-(b ^ 2))) * (((-1 : ℝ) ^ k) * ((-1 : ℝ) ^ k)) *
          (√3 * √3 / 4) := by
      ring
    rw [e, hpp, h3] at h1
    linarith
  have hcont : ContinuousOn (fun r : ℝ => airyAi (-(r ^ 2))) (Icc a b) :=
    continuous_airyAi_neg_sq.continuousOn
  have hzero : ∃ r ∈ Ioo a b, airyAi (-(r ^ 2)) = 0 := by
    rcases lt_or_gt_of_ne (show airyAi (-(a ^ 2)) ≠ 0 from fun h => by
      rw [h, zero_mul] at hprod; exact lt_irrefl _ hprod) with hneg | hpos
    · have hbpos : 0 < airyAi (-(b ^ 2)) := by
        by_contra hh
        push Not at hh
        exact absurd hprod (not_lt.mpr (mul_nonneg_of_nonpos_of_nonpos hneg.le hh))
      obtain ⟨r, hr, hr0⟩ := intermediate_value_Ioo hab.le hcont ⟨hneg, hbpos⟩
      exact ⟨r, hr, hr0⟩
    · have hbneg : airyAi (-(b ^ 2)) < 0 := by
        by_contra hh
        push Not at hh
        exact absurd hprod (not_lt.mpr (mul_nonneg hpos.le hh))
      obtain ⟨r, hr, hr0⟩ := intermediate_value_Ioo' hab.le hcont ⟨hbneg, hpos⟩
      exact ⟨r, hr, hr0⟩
  obtain ⟨r, ⟨hra, hrb⟩, hr0⟩ := hzero
  refine ⟨r, ha0.trans hra, ?_, hr0⟩
  have h1 : 2 / 3 * a ^ 3 < 2 / 3 * r ^ 3 := by
    have := pow_lt_pow_left₀ hra ha0.le (by norm_num : 3 ≠ 0); linarith
  have h2 : 2 / 3 * r ^ 3 < 2 / 3 * b ^ 3 := by
    have := pow_lt_pow_left₀ hrb (ha0.trans hra).le (by norm_num : 3 ≠ 0); linarith
  rw [abs_lt]; constructor <;> linarith

/-- A window contains at most one zero (Rolle: `Ai'(-r²) ≠ 0` throughout the window). -/
lemma window_no_two {k : ℤ} (hk : 2 ≤ k) {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (wa : |2 / 3 * a ^ 3 - (k + 3 / 4) * π| < π / 3) (wb : |2 / 3 * b ^ 3 - (k + 3 / 4) * π| < π / 3)
    (za : airyAi (-(a ^ 2)) = 0) (zb : airyAi (-(b ^ 2)) = 0) : False := by
  obtain ⟨c, hc, hc0⟩ := exists_hasDerivAt_eq_zero hab
    continuous_airyAi_neg_sq.continuousOn (za.trans zb.symm)
    (fun x _ => hasDerivAt_airyAi_neg_sq x)
  have h1 : 2 / 3 * a ^ 3 < 2 / 3 * c ^ 3 := by
    have := pow_lt_pow_left₀ hc.1 ha.le (by norm_num : 3 ≠ 0); linarith
  have h2 : 2 / 3 * c ^ 3 < 2 / 3 * b ^ 3 := by
    have := pow_lt_pow_left₀ hc.2 (ha.trans hc.1).le (by norm_num : 3 ≠ 0); linarith
  have hw : |2 / 3 * c ^ 3 - (k + 3 / 4) * π| ≤ π / 3 := by
    rw [abs_lt] at wa wb
    rw [abs_le]; constructor <;> linarith
  obtain ⟨hc2, hs⟩ := window_facts hk hw
  have hne := airyAi'_neg_sq_ne_zero hc2 hs
  have hc0' : c ≠ 0 := by linarith
  have : airyAi' (-(c ^ 2)) * (-(2 * c)) ≠ 0 :=
    mul_ne_zero hne (neg_ne_zero.mpr (mul_ne_zero two_ne_zero hc0'))
  exact this hc0

/-- **Exactly one zero in each window** (variable `r = √y`): for every integer `k ≥ 2` there is a unique `r > 0`
with `|(2/3) r³ - (k + 3/4)π| < π/3` and `Ai(-r²) = 0`. -/
theorem airy_zero_window_existsUnique_r {k : ℤ} (hk : 2 ≤ k) :
    ∃! r : ℝ, 0 < r ∧ |2 / 3 * r ^ 3 - (k + 3 / 4) * π| < π / 3 ∧ airyAi (-(r ^ 2)) = 0 := by
  obtain ⟨r, hr, hw, hz⟩ := airy_zero_window_exists hk
  refine ⟨r, ⟨hr, hw, hz⟩, ?_⟩
  rintro r' ⟨hr', hw', hz'⟩
  rcases lt_trichotomy r' r with h | h | h
  · exact (window_no_two hk hr' h hw' hw hz' hz).elim
  · exact h
  · exact (window_no_two hk hr h hw hw' hz hz').elim

/-- **Location of the zeros** (variable `r = √y`): if `r ≥ 2` and `Ai(-r²) = 0`, there is an integer `k` with
`|(2/3) r³ - (k + 3/4)π| ≤ (2/5)/r³`. -/
theorem airy_zero_location_r {r : ℝ} (hr : 2 ≤ r) (hz : airyAi (-(r ^ 2)) = 0) :
    ∃ k : ℤ, |2 / 3 * r ^ 3 - (k + 3 / 4) * π| ≤ 2 / 5 / r ^ 3 := by
  have hr0 : 0 < r := by linarith
  have h := airyAi_neg_sq_asymptotic hr0
  rw [hz, zero_sub, abs_neg] at h
  set φ := 2 / 3 * r ^ 3 - π / 4 with hφ
  have hs : 0 < √r := Real.sqrt_pos.mpr hr0
  have hT : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
  have hM : 0 < √π * √r := by positivity
  have hc : |Real.cos φ| ≤ √π / (8 * r ^ 3) := by
    rw [abs_div, abs_of_pos hM, div_le_iff₀ hM] at h
    calc |Real.cos φ| ≤ 1 / (8 * (√r * r ^ 3)) * (√π * √r) := h
      _ = √π / (8 * r ^ 3) := by field_simp
  -- nearest half-integer point
  set q := (φ - π / 2) / π with hq
  set k : ℤ := round q with hk
  have hqk : |q - k| ≤ 1 / 2 := abs_sub_round q
  set x := φ - (k + 1 / 2) * π with hx
  have hxq : x = π * (q - k) := by
    rw [hx, hq]; field_simp; ring
  have hxabs : |x| ≤ π / 2 := by
    rw [hxq, abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos]
  have hφx : φ = x + (k + 1 / 2) * π := by rw [hx]; ring
  have hcs : |Real.cos φ| = |Real.sin x| := by rw [hφx, abs_cos_shift]
  have hxs : |x| ≤ π / 2 * |Real.sin x| := by
    have key : ∀ y : ℝ, 0 ≤ y → y ≤ π / 2 → y ≤ π / 2 * Real.sin y := by
      intro y h0 h1
      have := Real.mul_le_sin h0 h1
      have hπ := Real.pi_pos
      calc y = π / 2 * (2 / π * y) := by field_simp
        _ ≤ π / 2 * Real.sin y := mul_le_mul_of_nonneg_left this (by positivity)
    rcases le_total 0 x with h0 | h0
    · rw [abs_of_nonneg h0]
      exact (key x h0 (by linarith [(abs_le.mp hxabs).2])).trans
        (mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity))
    · rw [abs_of_nonpos h0]
      have := key (-x) (by linarith) (by linarith [(abs_le.mp hxabs).1])
      rw [Real.sin_neg] at this
      exact this.trans (mul_le_mul_of_nonneg_left (neg_le_abs _) (by positivity))
  refine ⟨k, ?_⟩
  have e : 2 / 3 * r ^ 3 - (k + 3 / 4) * π = x := by rw [hx, hφ]; ring
  rw [e]
  have hr3 : 0 < r ^ 3 := by positivity
  have hπ1 : π < 3.15 := Real.pi_lt_d2
  have hπ2 : √π < 1.78 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num; linarith
  calc |x| ≤ π / 2 * |Real.sin x| := hxs
    _ = π / 2 * |Real.cos φ| := by rw [hcs]
    _ ≤ π / 2 * (√π / (8 * r ^ 3)) := mul_le_mul_of_nonneg_left hc (by positivity)
    _ = π * √π / 16 / r ^ 3 := by field_simp; ring
    _ ≤ 2 / 5 / r ^ 3 := by
        apply div_le_div_of_nonneg_right _ hr3.le
        nlinarith [Real.sqrt_nonneg π, Real.pi_pos]

/-- **Zeros of `Ai` on the negative axis, asymptotic location** (DLMF 9.9.6 with explicit error): if `y ≥ 4` and
`Ai(-y) = 0` there is an integer `k` with `|(2/3) y^{3/2} - (k + 3/4)π| ≤ (2/5) y^{-3/2}`. -/
theorem airy_zero_location {y : ℝ} (hy : 4 ≤ y) (hz : airyAi (-y) = 0) :
    ∃ k : ℤ, |2 / 3 * y ^ (3 / 2 : ℝ) - (k + 3 / 4) * π| ≤ 2 / 5 * y ^ (-(3 / 2) : ℝ) := by
  have hy0 : 0 < y := by linarith
  have hr : 2 ≤ √y := by
    rw [show (2 : ℝ) = √(2 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  obtain ⟨k, hk⟩ := airy_zero_location_r hr (by rw [Real.sq_sqrt hy0.le]; exact hz)
  refine ⟨k, ?_⟩
  rw [← sqrt_cube_eq_rpow hy0, Real.rpow_neg hy0.le, ← sqrt_cube_eq_rpow hy0]
  convert hk using 1
  field_simp

/-- **Exactly one zero in each window**: for every integer `k ≥ 2` there is a unique `y > 0` with
`|(2/3) y^{3/2} - (k + 3/4)π| < π/3` and `Ai(-y) = 0`. -/
theorem airy_zero_window_existsUnique {k : ℤ} (hk : 2 ≤ k) :
    ∃! y : ℝ, 0 < y ∧ |2 / 3 * y ^ (3 / 2 : ℝ) - (k + 3 / 4) * π| < π / 3 ∧ airyAi (-y) = 0 := by
  obtain ⟨r, ⟨hr, hw, hz⟩, hu⟩ := airy_zero_window_existsUnique_r hk
  refine ⟨r ^ 2, ⟨by positivity, ?_, ?_⟩, ?_⟩
  · have : (r ^ 2) ^ (3 / 2 : ℝ) = r ^ 3 := by
      rw [← Real.rpow_natCast r 2, ← Real.rpow_mul hr.le]; norm_num
    rw [this]; exact hw
  · exact hz
  · rintro y ⟨hy, hw', hz'⟩
    have hs : 0 < √y := Real.sqrt_pos.mpr hy
    have := hu (√y) ⟨hs, by rw [sqrt_cube_eq_rpow hy]; exact hw', by rw [Real.sq_sqrt hy.le]; exact hz'⟩
    rw [← this, Real.sq_sqrt hy.le]

/-- info: 'FormalResearch.Special.airy_zero_location' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airy_zero_location

/-- info: 'FormalResearch.Special.airy_zero_window_existsUnique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airy_zero_window_existsUnique

end FormalResearch.Special
