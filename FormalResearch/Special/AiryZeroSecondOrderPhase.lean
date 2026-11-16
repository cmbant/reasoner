module

public import FormalResearch.Special.AiryZeroSecondOrderChi
public import FormalResearch.Special.AiryZeroLemmaZ

/-!
# The phase of the `n`-th zero of `Ai` to `O(ξ^{-3})`: `ξ_n - (5/72)/ξ_n = (n - 1/4)π + O(ξ_n^{-3})`

Let `r = √(-a_n)` and `ξ_n = (2/3) r³`.  `AiryZeroLabel` (`airyZero_phase_r`) gives `|ξ_n - (n - 1/4)π| ≤ (2/5)/r³`.
Here this is sharpened using `airySO_Ai_neg_sq` (the `u₂`-corrected expansion, `AiryZeroSecondOrderChi`): at a zero,
with `ε = ξ_n - (n - 1/4)π` and `φ = ξ_n - π/4 = (n - 1/2)π + ε`, `cos φ = ± sin ε` and `sin φ = ∓ cos ε`, so the
expansion gives `|a sin ε - t cos ε| ≤ r^{-9}` with `a = 1 - 385/(4608 r⁶)`, `t = 5/(48 r³)`.  Since `ε = O(r^{-3})` is
already known, `sin ε = ε + O(r^{-9})`, `cos ε = 1 + O(r^{-6})` and `a = 1 + O(r^{-6})` give

* `airySO_phase_alg`: the real-variable lemma, `|ε| ≤ (2/5) q`, `0 < q ≤ 1/8`,
  `|(1 - (385/4608) q²) sin ε - (5/48) q cos ε| ≤ q³`  imply  `|ε - (5/48) q| ≤ (11/10) q³`;
* **`airyZero_phase_second`**: for `n ≥ 2`, `r = √(-a_n)`:
  `|(2/3) r³ - (n - 1/4)π - 5/(48 r³)| ≤ (11/10) r^{-9}`, i.e. `ξ_n - (5/72)/ξ_n = (n - 1/4)π + O(ξ_n^{-3})`
  (the zero condition for the `u₁`-corrected phase; the `ξ^{-2}` term is absent because it multiplies `cos φ ≈ 0`).

Numerically (mpmath, 30 digits, `2 ≤ n ≤ 3000`): `r⁹ ((2/3) r³ - (n - 1/4)π - 5/(48 r³))` equals `-0.1098` (`n = 2`) and
converges to `-0.11990` as `n → ∞` (the `u₃`-sized value), far inside the proved `11/10`.

Proved here: both statements.  The next order of the phase is `airyZero_phase_third` (`AiryZeroThirdPhase`).
-/

@[expose] public section

open Set
open scoped Real

namespace FormalResearch.Special

/-- The real-variable core: from `|ε| ≤ (2/5) q` and `|a sin ε - t cos ε| ≤ q³` (`a = 1 - (385/4608) q²`,
`t = (5/48) q`) to `|ε - t| ≤ (11/10) q³`. -/
lemma airySO_phase_alg {ε q : ℝ} (hq0 : 0 < q) (hq : q ≤ 1 / 8) (hε : |ε| ≤ 2 / 5 * q)
    (h : |(1 - 385 / 4608 * q ^ 2) * Real.sin ε - 5 / 48 * q * Real.cos ε| ≤ q ^ 3) :
    |ε - 5 / 48 * q| ≤ 11 / 10 * q ^ 3 := by
  have hε1 : |ε| ≤ 1 := by nlinarith
  have hsin := Real.sin_bound hε1
  have hcos1 := Real.cos_le_one ε
  have hcos2 := Real.one_sub_sq_div_two_le_cos (x := ε)
  have hε2 : ε ^ 2 ≤ 4 / 25 * q ^ 2 := by
    have := sq_le_sq' (by linarith [abs_le.mp hε]) (abs_le.mp hε).2
    nlinarith [sq_abs ε, abs_nonneg ε]
  have hε3 : |ε| ^ 3 ≤ 8 / 125 * q ^ 3 := by
    have := pow_le_pow_left₀ (abs_nonneg ε) hε 3
    nlinarith
  have hε5 : |ε| ^ 5 ≤ 32 / 3125 * q ^ 5 := by
    have := pow_le_pow_left₀ (abs_nonneg ε) hε 5
    nlinarith
  have hsin' : |Real.sin ε - ε| ≤ |ε| ^ 3 / 6 + |ε| ^ 5 / 100 := by
    have e : Real.sin ε - ε = (Real.sin ε - (ε - ε ^ 3 / 6)) - ε ^ 3 / 6 := by ring
    rw [e]
    refine (abs_sub _ _).trans ?_
    have : |ε ^ 3 / 6| = |ε| ^ 3 / 6 := by rw [abs_div, abs_pow]; norm_num
    rw [this]
    linarith
  set a : ℝ := 1 - 385 / 4608 * q ^ 2 with ha
  have ha0 : 0 ≤ a := by rw [ha]; nlinarith
  have ha1 : a ≤ 1 := by rw [ha]; nlinarith
  -- a ε - t = X + a (ε - sin ε) + t (cos ε - 1)
  have key : a * ε - 5 / 48 * q = ((a * Real.sin ε - 5 / 48 * q * Real.cos ε) + a * (ε - Real.sin ε)) +
      5 / 48 * q * (Real.cos ε - 1) := by ring
  have b1 : |a * (ε - Real.sin ε)| ≤ |ε| ^ 3 / 6 + |ε| ^ 5 / 100 := by
    rw [abs_mul, abs_of_nonneg ha0, abs_sub_comm]
    calc a * |Real.sin ε - ε| ≤ 1 * |Real.sin ε - ε| := mul_le_mul_of_nonneg_right ha1 (abs_nonneg _)
      _ ≤ _ := by linarith
  have b2 : |5 / 48 * q * (Real.cos ε - 1)| ≤ 5 / 48 * q * (ε ^ 2 / 2) := by
    rw [abs_mul, abs_of_nonneg (by positivity), abs_of_nonpos (by linarith)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith
  have b3 : |a * ε - 5 / 48 * q| ≤ q ^ 3 + (|ε| ^ 3 / 6 + |ε| ^ 5 / 100) + 5 / 48 * q * (ε ^ 2 / 2) := by
    rw [key]
    refine (abs_add_le _ _).trans ?_
    refine add_le_add ((abs_add_le _ _).trans (add_le_add h b1)) b2
  have hq3 : q ^ 5 ≤ 1 / 64 * q ^ 3 := by
    have h2 : q ^ 2 ≤ 1 / 64 := by nlinarith
    calc q ^ 5 = q ^ 3 * q ^ 2 := by ring
      _ ≤ q ^ 3 * (1 / 64) := mul_le_mul_of_nonneg_left h2 (pow_pos hq0 3).le
      _ = _ := by ring
  have b4 : |a * ε - 5 / 48 * q| ≤ 102 / 100 * q ^ 3 := by
    have : 5 / 48 * q * (ε ^ 2 / 2) ≤ 5 / 48 * q * (2 / 25 * q ^ 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    nlinarith [pow_pos hq0 3]
  have b5 : |(1 - a) * ε| ≤ 34 / 1000 * q ^ 3 := by
    rw [abs_mul, show 1 - a = 385 / 4608 * q ^ 2 by rw [ha]; ring, abs_of_nonneg (by positivity)]
    calc 385 / 4608 * q ^ 2 * |ε| ≤ 385 / 4608 * q ^ 2 * (2 / 5 * q) := by gcongr
      _ ≤ _ := by nlinarith [pow_pos hq0 3]
  have e2 : ε - 5 / 48 * q = (a * ε - 5 / 48 * q) + (1 - a) * ε := by ring
  rw [e2]
  refine (abs_add_le _ _).trans ?_
  linarith [pow_pos hq0 3]

/-- `cos` and `sin` at the zero phase: with `φ = ((n : ℝ) - 1/2) π + ε`, `cos φ = (-1)^n sin ε`, `sin φ = -(-1)^n cos ε`. -/
lemma airySO_trig_shift (n : ℕ) (ε : ℝ) :
    Real.cos (((n : ℝ) - 1 / 2) * π + ε) = (-1) ^ n * Real.sin ε ∧
      Real.sin (((n : ℝ) - 1 / 2) * π + ε) = -((-1) ^ n * Real.cos ε) := by
  have e : ((n : ℝ) - 1 / 2) * π + ε = (ε - π / 2) + n * π := by ring
  rw [e, Real.cos_add_nat_mul_pi, Real.sin_add_nat_mul_pi, Real.cos_sub_pi_div_two, Real.sin_sub_pi_div_two]
  constructor <;> ring

/-- **The zero phase to `O(ξ^{-3})`** (DLMF 9.9.18, phase form): for `n ≥ 2` and `r = √(-a_n)`,
`|(2/3) r³ - (n - 1/4)π - 5/(48 r³)| ≤ (11/10)/r⁹`. -/
theorem airyZero_phase_second {n : ℕ} (hn : 2 ≤ n) :
    |2 / 3 * airyZeroRoot n ^ 3 - ((n : ℝ) - 1 / 4) * π - 5 / (48 * airyZeroRoot n ^ 3)| ≤
      11 / 10 * (1 / airyZeroRoot n ^ 9) := by
  set r := airyZeroRoot n with hr
  have hr0 : 0 < r := airyZeroRoot_pos n
  have hr2 : 2 < r := two_lt_airyZeroRoot hn
  have hr3 : 8 < r ^ 3 := by nlinarith [pow_lt_pow_left₀ hr2 (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : 3 ≠ 0)]
  set ε := 2 / 3 * r ^ 3 - ((n : ℝ) - 1 / 4) * π with hεdef
  set q := 1 / r ^ 3 with hq
  have hq0 : 0 < q := by positivity
  have hq8 : q ≤ 1 / 8 := by
    rw [hq, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hph : |ε| ≤ 2 / 5 * q := by
    have := airyZero_phase_r hn
    rw [← hr] at this
    rw [hq]
    calc |ε| ≤ 2 / 5 / r ^ 3 := this
      _ = _ := by ring
  have hz := airySO_Ai_neg_sq hr0
  rw [← airyZero_eq_neg_root_sq n, airyAi_airyZero n] at hz
  have hφ : 2 / 3 * r ^ 3 - π / 4 = ((n : ℝ) - 1 / 2) * π + ε := by rw [hεdef]; ring
  rw [hφ] at hz
  obtain ⟨hc, hs⟩ := airySO_trig_shift n ε
  rw [hc, hs] at hz
  have hsr : 0 < √r := Real.sqrt_pos.mpr hr0
  have hT : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
  have hT2 : √π < 2 := sqrtpi_lt_two
  set X := (1 - 385 / 4608 * q ^ 2) * Real.sin ε - 5 / 48 * q * Real.cos ε with hX
  have hX' : 1 / (√π * √r) * ((1 - 385 / (4608 * r ^ 6)) * ((-1) ^ n * Real.sin ε) +
      5 / (48 * r ^ 3) * (-((-1) ^ n * Real.cos ε))) = (-1) ^ n * (1 / (√π * √r) * X) := by
    rw [hX, hq]
    field_simp
    ring
  have hz2 : |(-1 : ℝ) ^ n * (1 / (√π * √r) * X)| = 1 / (√π * √r) * |X| := by
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (√π * √r))]
  rw [zero_sub, abs_neg, hX', hz2] at hz
  have hXb : |X| ≤ q ^ 3 := by
    have h1 : 1 / (√π * √r) * |X| ≤ 1 / 2 * (1 / (√r * r ^ 9)) := hz
    have h2 : |X| ≤ √π / 2 * (1 / r ^ 9) := by
      have e : 1 / (√π * √r) * |X| ≤ (1 / (√π * √r)) * (√π / 2 * (1 / r ^ 9)) := by
        refine h1.trans (le_of_eq ?_)
        field_simp
      exact le_of_mul_le_mul_left e (by positivity)
    have e3 : q ^ 3 = 1 / r ^ 9 := by rw [hq]; field_simp
    rw [e3]
    calc |X| ≤ √π / 2 * (1 / r ^ 9) := h2
      _ ≤ 1 * (1 / r ^ 9) := by gcongr; linarith
      _ = _ := one_mul _
  have := airySO_phase_alg hq0 hq8 hph hXb
  have e5 : 5 / 48 * q = 5 / (48 * r ^ 3) := by rw [hq]; field_simp
  have e6 : q ^ 3 = 1 / r ^ 9 := by rw [hq]; field_simp
  rw [e5, e6] at this
  have e7 : 2 / 3 * r ^ 3 - ((n : ℝ) - 1 / 4) * π - 5 / (48 * r ^ 3) = ε - 5 / (48 * r ^ 3) := by
    rw [hεdef]
  rw [e7]
  exact this

/-- info: 'FormalResearch.Special.airyZero_phase_second' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyZero_phase_second

end FormalResearch.Special
