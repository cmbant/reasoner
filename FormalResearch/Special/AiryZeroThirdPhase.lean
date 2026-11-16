module

public import FormalResearch.Special.AiryZeroThirdChi
public import FormalResearch.Special.AiryZeroSecondOrderPhase

/-!
# The phase of the `n`-th zero of `Ai` to `O(ξ^{-5})`

Let `r = √(-a_n)` and `s = r³`.  `AiryZeroSecondOrderPhase` gives `|(2/3)s - (n - 1/4)π - 5/(48 s)| ≤ (11/10)/s³`.  Using
`airyT3_Ai_neg_sq` (the `u₄`-corrected expansion, `AiryZeroThirdChi`) with
`ε = (2/3)s - (n - 1/4)π` and `q = 1/s`, the zero condition becomes
`|a sin ε - t cos ε| ≤ 18 q⁵` with `a = 1 - (385/4608) q² + (37182145/127401984) q⁴`, `t = (5/48) q - (85085/663552) q³`.
Expanding `sin`, `cos` (Mathlib `Real.sin_bound`, `Real.cos_bound`) and substituting the known `ε = (5/48) q + O(q³)`:

* `airyT3_phase_alg`: the real core, `0 < q ≤ 1/8`, `|ε - (5/48)q| ≤ (11/10)q³`, `|a sin ε - t cos ε| ≤ 18 q⁵` imply
  `|ε - (5/48) q + (1105/9216) q³| ≤ 19 q⁵`;
* **`airyZero_phase_third`**: for `n ≥ 2`, `r = √(-a_n)`:
  `|(2/3) r³ - (n - 1/4)π - 5/(48 r³) + 1105/(9216 r⁹)| ≤ 19/r^{15}`.

The coefficient `-1105/9216 = -85085/663552 - (1/3)(5/48)³ + (5/48)(385/4608)` collects the `u₃` coefficient of `t`, the cube
of the leading term from `sin ε ≈ ε - ε³/6`, `cos ε ≈ 1 - ε²/2`, and the `u₂` coefficient of `a` (divided out).

Numerically (mpmath, 60 digits, `2 ≤ n ≤ 59` and `n = 100, 300, 1000`): `s⁵ ((2/3) s - (n - 1/4)π - 5/(48 s) + 1105/(9216 s³))`
increases from `0.690` (`n = 2`) to `0.8425` (`n = 1000`), far inside the proved `19`.

Proved here: both statements.  **Not formalised:** the sharp `s^{-5}` coefficient (`≈ 0.8425`).
-/

@[expose] public section

open Set
open scoped Real

namespace FormalResearch.Special

/-- `|q^i ζ^j| ≤ (1/8)^i (11/10)^j` for `0 ≤ q ≤ 1/8`, `|ζ| ≤ 11/10`. -/
lemma airyT3_mono_le {q ζ : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1 / 8) (hζ : |ζ| ≤ 11 / 10) (i j : ℕ) :
    |q ^ i * ζ ^ j| ≤ (1 / 8) ^ i * (11 / 10) ^ j := by
  rw [abs_mul, abs_pow, abs_pow, abs_of_nonneg hq0]
  exact mul_le_mul (pow_le_pow_left₀ hq0 hq i) (pow_le_pow_left₀ (abs_nonneg _) hζ j) (by positivity)
    (by positivity)

/-- The remainder polynomial `P(q, ζ)` is at most `1/25` in absolute value. -/
lemma airyT3_P_le {q ζ : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1 / 8) (hζ : |ζ| ≤ 11 / 10) :
    |(-181752725 / 6115295232 : ℝ) - 25 / 4608 * ζ + 4647768125 / 84537841287168 * q ^ 2 +
        821975 / 63700992 * (q ^ 2 * ζ) + 929553625 / 587068342272 * (q ^ 4 * ζ) +
        39655 / 663552 * (q ^ 4 * ζ ^ 2) + 1 / 6 * (q ^ 4 * ζ ^ 3) +
        185910725 / 12230590464 * (q ^ 6 * ζ ^ 2) - 385 / 27648 * (q ^ 6 * ζ ^ 3) +
        37182145 / 764411904 * (q ^ 8 * ζ ^ 3)| ≤ 1 / 25 := by
  have h20 := abs_le.mp (airyT3_mono_le hq0 hq hζ 2 0)
  have h21 := abs_le.mp (airyT3_mono_le hq0 hq hζ 2 1)
  have h41 := abs_le.mp (airyT3_mono_le hq0 hq hζ 4 1)
  have h42 := abs_le.mp (airyT3_mono_le hq0 hq hζ 4 2)
  have h43 := abs_le.mp (airyT3_mono_le hq0 hq hζ 4 3)
  have h62 := abs_le.mp (airyT3_mono_le hq0 hq hζ 6 2)
  have h63 := abs_le.mp (airyT3_mono_le hq0 hq hζ 6 3)
  have h83 := abs_le.mp (airyT3_mono_le hq0 hq hζ 8 3)
  have hz := abs_le.mp hζ
  simp only [pow_zero, mul_one] at h20
  simp only [pow_one] at h21 h41
  rw [abs_le]
  constructor <;> norm_num at h20 h21 h41 h42 h43 h62 h63 h83 ⊢ <;>
    linarith [h20.1, h20.2, h21.1, h21.2, h41.1, h41.2, h42.1, h42.2, h43.1, h43.2, h62.1, h62.2,
      h63.1, h63.2, h83.1, h83.2, hz.1, hz.2]

/-- **The real core.** For `0 < q ≤ 1/8`, `|ε - (5/48) q| ≤ (11/10) q³` and
`|a sin ε - t cos ε| ≤ 18 q⁵` (`a = 1 - (385/4608) q² + (37182145/127401984) q⁴`,
`t = (5/48) q - (85085/663552) q³`): `|ε - (5/48) q + (1105/9216) q³| ≤ 19 q⁵`. -/
lemma airyT3_phase_alg {ε q : ℝ} (hq0 : 0 < q) (hq : q ≤ 1 / 8) (hη : |ε - 5 / 48 * q| ≤ 11 / 10 * q ^ 3)
    (hX : |(1 - 385 / 4608 * q ^ 2 + 37182145 / 127401984 * q ^ 4) * Real.sin ε -
        (5 / 48 * q - 85085 / 663552 * q ^ 3) * Real.cos ε| ≤ 18 * q ^ 5) :
    |ε - 5 / 48 * q + 1105 / 9216 * q ^ 3| ≤ 19 * q ^ 5 := by
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = 1 - 385 / 4608 * q ^ 2 + 37182145 / 127401984 * q ^ 4 := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = 5 / 48 * q - 85085 / 663552 * q ^ 3 := ⟨_, rfl⟩
  rw [← ha, ← ht] at hX
  have hq2 : q ^ 2 ≤ 1 / 64 := by nlinarith
  have hq3 : q ^ 3 ≤ 1 / 64 * q := by nlinarith [pow_pos hq0 3]
  have hq5 : 0 < q ^ 5 := pow_pos hq0 5
  have hq4 : q ^ 4 ≤ 1 / 64 * q ^ 2 := by nlinarith [pow_pos hq0 4]
  -- size of ε
  have hε : |ε| ≤ 1215 / 10000 * q := by
    have h1 : |ε| ≤ |5 / 48 * q| + |ε - 5 / 48 * q| := by
      have := abs_add_le (5 / 48 * q) (ε - 5 / 48 * q)
      simpa using this
    rw [abs_of_pos (by positivity : (0 : ℝ) < 5 / 48 * q)] at h1
    nlinarith
  have hε1 : |ε| ≤ 1 := by nlinarith
  have hε4 : |ε| ^ 4 ≤ (1215 / 10000) ^ 4 * q ^ 4 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hε 4
  have hε5 : |ε| ^ 5 ≤ (1215 / 10000) ^ 5 * q ^ 5 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hε 5
  have hs := Real.sin_bound hε1
  have hc := Real.cos_bound hε1
  obtain ⟨Rs, hRs⟩ : ∃ Rs : ℝ, Rs = Real.sin ε - (ε - ε ^ 3 / 6) := ⟨_, rfl⟩
  obtain ⟨Rc, hRc⟩ : ∃ Rc : ℝ, Rc = Real.cos ε - (1 - ε ^ 2 / 2) := ⟨_, rfl⟩
  rw [← hRs] at hs
  rw [← hRc] at hc
  have ha0 : 0 ≤ a := by rw [ha]; nlinarith
  have ha1 : a ≤ 1 := by rw [ha]; nlinarith
  have ht0 : 0 ≤ t := by rw [ht]; nlinarith
  have ht1 : t ≤ 5 / 48 * q := by rw [ht]; nlinarith [pow_pos hq0 3]
  -- Y' = X - a Rs + t Rc
  have hY : |(a * ε - t) - (a * ε ^ 3 / 6 - t * ε ^ 2 / 2)| ≤ 1801 / 100 * q ^ 5 := by
    have e : (a * ε - t) - (a * ε ^ 3 / 6 - t * ε ^ 2 / 2) =
        (a * Real.sin ε - t * Real.cos ε) - a * Rs + t * Rc := by rw [hRs, hRc]; ring
    rw [e]
    have b1 : |a * Rs| ≤ 1 / 1000000 * q ^ 5 := by
      rw [abs_mul, abs_of_nonneg ha0]
      calc a * |Rs| ≤ 1 * |Rs| := mul_le_mul_of_nonneg_right ha1 (abs_nonneg _)
        _ ≤ |ε| ^ 5 / 100 := by linarith
        _ ≤ _ := by nlinarith
    have b2 : |t * Rc| ≤ 2 / 1000000 * q ^ 5 := by
      rw [abs_mul, abs_of_nonneg ht0]
      have h1 : |Rc| ≤ 5 / 96 * ((1215 / 10000) ^ 4 * q ^ 4) := by nlinarith
      calc t * |Rc| ≤ (5 / 48 * q) * (5 / 96 * ((1215 / 10000) ^ 4 * q ^ 4)) :=
            mul_le_mul ht1 h1 (abs_nonneg _) (by positivity)
        _ ≤ _ := by nlinarith [pow_pos hq0 5]
    have h3 : |(a * Real.sin ε - t * Real.cos ε) - a * Rs + t * Rc| ≤
        |a * Real.sin ε - t * Real.cos ε| + |a * Rs| + |t * Rc| := by
      have := abs_add_le ((a * Real.sin ε - t * Real.cos ε) - a * Rs) (t * Rc)
      have := abs_sub (a * Real.sin ε - t * Real.cos ε) (a * Rs)
      linarith
    linarith
  -- the substitution ε = 5/48 q + ζ q³
  obtain ⟨ζ, hζdef⟩ : ∃ ζ : ℝ, ζ = (ε - 5 / 48 * q) / q ^ 3 := ⟨_, rfl⟩
  have hq3p : 0 < q ^ 3 := pow_pos hq0 3
  have hζ : |ζ| ≤ 11 / 10 := by
    rw [hζdef, abs_div, abs_of_pos hq3p, div_le_iff₀ hq3p]; linarith
  have hεζ : ε = 5 / 48 * q + ζ * q ^ 3 := by rw [hζdef]; field_simp; ring
  have hP := airyT3_P_le hq0.le hq hζ
  have hid : (ε - 5 / 48 * q + 1105 / 9216 * q ^ 3) =
      ((a * ε - t) - (a * ε ^ 3 / 6 - t * ε ^ 2 / 2)) + (1 - a) * (ζ * q ^ 3) +
        q ^ 5 * ((-181752725 / 6115295232 : ℝ) - 25 / 4608 * ζ + 4647768125 / 84537841287168 * q ^ 2 +
        821975 / 63700992 * (q ^ 2 * ζ) + 929553625 / 587068342272 * (q ^ 4 * ζ) +
        39655 / 663552 * (q ^ 4 * ζ ^ 2) + 1 / 6 * (q ^ 4 * ζ ^ 3) +
        185910725 / 12230590464 * (q ^ 6 * ζ ^ 2) - 385 / 27648 * (q ^ 6 * ζ ^ 3) +
        37182145 / 764411904 * (q ^ 8 * ζ ^ 3)) := by
    rw [ha, ht, hεζ]; ring
  rw [hid]
  have b3 : |(1 - a) * (ζ * q ^ 3)| ≤ 1 / 10 * q ^ 5 := by
    have h1a : 0 ≤ 1 - a := by linarith
    have h1b : 1 - a ≤ 385 / 4608 * q ^ 2 := by
      have : 0 ≤ q ^ 4 := by positivity
      rw [ha]; linarith
    rw [abs_mul, abs_of_nonneg h1a, abs_mul, abs_of_pos hq3p]
    have : |ζ| * q ^ 3 ≤ 11 / 10 * q ^ 3 := mul_le_mul_of_nonneg_right hζ hq3p.le
    calc (1 - a) * (|ζ| * q ^ 3) ≤ (385 / 4608 * q ^ 2) * (11 / 10 * q ^ 3) :=
          mul_le_mul h1b this (by positivity) (by positivity)
      _ = (385 / 4608 * (11 / 10)) * q ^ 5 := by ring
      _ ≤ 1 / 10 * q ^ 5 := mul_le_mul_of_nonneg_right (by norm_num) hq5.le
  have b4 : |q ^ 5 * ((-181752725 / 6115295232 : ℝ) - 25 / 4608 * ζ + 4647768125 / 84537841287168 * q ^ 2 +
        821975 / 63700992 * (q ^ 2 * ζ) + 929553625 / 587068342272 * (q ^ 4 * ζ) +
        39655 / 663552 * (q ^ 4 * ζ ^ 2) + 1 / 6 * (q ^ 4 * ζ ^ 3) +
        185910725 / 12230590464 * (q ^ 6 * ζ ^ 2) - 385 / 27648 * (q ^ 6 * ζ ^ 3) +
        37182145 / 764411904 * (q ^ 8 * ζ ^ 3))| ≤ 1 / 25 * q ^ 5 := by
    rw [abs_mul, abs_of_pos hq5, mul_comm]
    exact mul_le_mul_of_nonneg_right hP hq5.le
  have := abs_add_le (((a * ε - t) - (a * ε ^ 3 / 6 - t * ε ^ 2 / 2)) + (1 - a) * (ζ * q ^ 3))
    (q ^ 5 * ((-181752725 / 6115295232 : ℝ) - 25 / 4608 * ζ + 4647768125 / 84537841287168 * q ^ 2 +
        821975 / 63700992 * (q ^ 2 * ζ) + 929553625 / 587068342272 * (q ^ 4 * ζ) +
        39655 / 663552 * (q ^ 4 * ζ ^ 2) + 1 / 6 * (q ^ 4 * ζ ^ 3) +
        185910725 / 12230590464 * (q ^ 6 * ζ ^ 2) - 385 / 27648 * (q ^ 6 * ζ ^ 3) +
        37182145 / 764411904 * (q ^ 8 * ζ ^ 3)))
  have h2 := abs_add_le ((a * ε - t) - (a * ε ^ 3 / 6 - t * ε ^ 2 / 2)) ((1 - a) * (ζ * q ^ 3))
  linarith

lemma airyT3_sqrtpi_le : √π ≤ 9 / 5 := by
  rw [Real.sqrt_le_iff]
  exact ⟨by norm_num, by nlinarith [Real.pi_lt_d2]⟩

/-- **The zero phase to `O(ξ^{-5})`**: for `n ≥ 2` and `r = √(-a_n)`,
`|(2/3) r³ - (n - 1/4)π - 5/(48 r³) + 1105/(9216 r⁹)| ≤ 19/r^{15}`. -/
theorem airyZero_phase_third {n : ℕ} (hn : 2 ≤ n) :
    |2 / 3 * airyZeroRoot n ^ 3 - ((n : ℝ) - 1 / 4) * π - 5 / (48 * airyZeroRoot n ^ 3) +
        1105 / (9216 * airyZeroRoot n ^ 9)| ≤ 19 * (1 / airyZeroRoot n ^ 15) := by
  set r := airyZeroRoot n with hr
  have hr0 : 0 < r := airyZeroRoot_pos n
  have hr2 : 2 < r := two_lt_airyZeroRoot hn
  have hr3 : 8 < r ^ 3 := by nlinarith [pow_lt_pow_left₀ hr2 (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : 3 ≠ 0)]
  set ε := 2 / 3 * r ^ 3 - ((n : ℝ) - 1 / 4) * π with hεdef
  set q := 1 / r ^ 3 with hq
  have hq0 : 0 < q := by positivity
  have hq8 : q ≤ 1 / 8 := by
    rw [hq, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hη : |ε - 5 / 48 * q| ≤ 11 / 10 * q ^ 3 := by
    have h := airyZero_phase_second hn
    rw [← hr] at h
    have e1 : 5 / 48 * q = 5 / (48 * r ^ 3) := by rw [hq]; field_simp
    have e2 : q ^ 3 = 1 / r ^ 9 := by rw [hq]; field_simp
    rw [e1, e2]
    exact h
  have hz := airyT3_Ai_neg_sq hr0
  rw [← airyZero_eq_neg_root_sq n, airyAi_airyZero n] at hz
  have hφ : 2 / 3 * r ^ 3 - π / 4 = ((n : ℝ) - 1 / 2) * π + ε := by rw [hεdef]; ring
  rw [hφ] at hz
  obtain ⟨hc, hs⟩ := airySO_trig_shift n ε
  rw [hc, hs] at hz
  have hsr : 0 < √r := Real.sqrt_pos.mpr hr0
  have hT : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
  have hT2 := airyT3_sqrtpi_le
  set X := (1 - 385 / 4608 * q ^ 2 + 37182145 / 127401984 * q ^ 4) * Real.sin ε -
    (5 / 48 * q - 85085 / 663552 * q ^ 3) * Real.cos ε with hX
  have hX' : 1 / (√π * √r) * ((1 - 385 / (4608 * r ^ 6) + 37182145 / (127401984 * r ^ 12)) *
      ((-1) ^ n * Real.sin ε) +
      (5 / (48 * r ^ 3) - 85085 / (663552 * r ^ 9)) * (-((-1) ^ n * Real.cos ε))) =
      (-1) ^ n * (1 / (√π * √r) * X) := by
    rw [hX, hq]
    field_simp
    ring
  have hz2 : |(-1 : ℝ) ^ n * (1 / (√π * √r) * X)| = 1 / (√π * √r) * |X| := by
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (√π * √r))]
  rw [zero_sub, abs_neg, hX', hz2] at hz
  have hXb : |X| ≤ 18 * q ^ 5 := by
    have h1 : 1 / (√π * √r) * |X| ≤ 10 * (1 / (√r * r ^ 15)) := hz
    have h2 : |X| ≤ 10 * √π * (1 / r ^ 15) := by
      have e : 1 / (√π * √r) * |X| ≤ (1 / (√π * √r)) * (10 * √π * (1 / r ^ 15)) := by
        refine h1.trans (le_of_eq ?_)
        field_simp
      exact le_of_mul_le_mul_left e (by positivity)
    have e3 : q ^ 5 = 1 / r ^ 15 := by rw [hq]; field_simp
    rw [e3]
    calc |X| ≤ 10 * √π * (1 / r ^ 15) := h2
      _ ≤ 18 * (1 / r ^ 15) := by gcongr; linarith
  have := airyT3_phase_alg hq0 hq8 hη hXb
  have e5 : 5 / 48 * q = 5 / (48 * r ^ 3) := by rw [hq]; field_simp
  have e6 : 1105 / 9216 * q ^ 3 = 1105 / (9216 * r ^ 9) := by rw [hq]; field_simp
  have e7 : q ^ 5 = 1 / r ^ 15 := by rw [hq]; field_simp
  rw [e5, e6, e7] at this
  have e8 : 2 / 3 * r ^ 3 - ((n : ℝ) - 1 / 4) * π - 5 / (48 * r ^ 3) + 1105 / (9216 * r ^ 9) =
      ε - 5 / (48 * r ^ 3) + 1105 / (9216 * r ^ 9) := by rw [hεdef]
  rw [e8]
  exact this

/-- info: 'FormalResearch.Special.airyT3_phase_alg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyT3_phase_alg

/-- info: 'FormalResearch.Special.airyZero_phase_third' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyZero_phase_third

end FormalResearch.Special
