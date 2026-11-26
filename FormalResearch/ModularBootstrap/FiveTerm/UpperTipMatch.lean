module

public import FormalResearch.ModularBootstrap.FiveTerm.UpperPhaseChart

/-!
# Renormalised tip-dipole boundary cancellation (FIVE-U; `pm:tip-match`, Lemma C14$_0$)

Source: `CFT/modular_bootstrap/paper/constant_term_slit_strip.tex`, Lemma C14$_0$ (`pm:tip-match`).

The slit coordinate `y = y(x)` is fixed by `cosh(π x) = √2 (1+y²)/(1-y²)` (`cts:s3`); the Langer phase is
`τ = (N(x)/k_tip)^{2/3}` (`tauPhase`).  Near the tip (`π(x-ξ_*) ≤ 1/10`, `τ ≤ 10⁻³`):

* `slit_sq_expansion`: `|y² - (π r/(2√2) + (π r)²/8)| ≤ (π r)³`, `r = x - ξ_*`;
* `slit_sq_tau`: `|y² - Yτ(1 + bτ)| ≤ 290 τ³`, `Y = π/(2√2)`, `b = 7π/(15√2) = Y - π/(30√2)`
  (the paper's `y_S = √(π/(2√2)) (λS)^{1/2} (1 + (7π/(30√2)) λS + O((λS)²))`);
* `slit_expansion_core`: with `(1-y²)³/(3y³) = 1/(3y³) - 1/y + y - y³/3`,
  `|(3k_tip/16)(1-y²)³/(3y³) - (2/(9π²)) τ^{-3/2} + (11√2/(45π)) τ^{-1/2}| ≤ 500 (2/(9π²)) τ^{1/2}`,
  using the closed form `k_tip = 32 (√Y)³/(9π²)` (`kTip_eq_slit`);
* **`tip_match`**: the statement of Lemma C14$_0$ in the paper's variables `c'`, `S`, `λ = (k_tip c')^{-2/3}`,
  `κ_comb = (3π/2)^{2/3}`: `𝒯(S) - |a_1|/(3πκ^{3/2}) S^{-3/2} - c_Sm^{(0)} λ/(π√κ) S^{-1/2}
  - g_{1,geo}^{(0)}|a_1| λ/(πκ^{3/2}) S^{-1/2} = O(c'^{-1}(λS)^{1/2})` with explicit constants, uniformly in
  `c' > 0`, `S > 0` with `λ S ≤ τ₀`.  The two negative powers of `S` cancel because
  `c_Sm^{(0)}/(π√κ) + g_{1,geo}^{(0)}|a_1|/(πκ^{3/2}) = -11√2|a_1|/(45π)`.

The O-constant is `500 · (2/(9π²)) |a_1| / k_tip`, `τ₀ = min(10⁻³, τ(ξ_* + 1/(10π))/2)`.  Numerically (quadrature, not in
Lean) the left side of `slit_expansion_core` divided by `τ^{1/2}` tends to about `0.246`, against the stated
`500 · 2/(9π²) ≈ 11.3`, so the constant is generous; the decimals are not claimed.  All results are proved unconditionally.
-/

@[expose] public section

open Real

namespace FormalResearch.ModularBootstrap.FiveTerm

open FormalResearch.Special FormalResearch.ModularBootstrap

/-- polynomial core of the slit expansion -/
lemma slit_core {z ri P q : ℝ} (hz0 : 0 < z) (hz1 : z ≤ 1 / 10) (hri : ri * ri = 1 / 2)
    (hri0 : 0 < ri) (hP1 : ri * z + z ^ 2 / 2 ≤ P)
    (hP2 : P ≤ ri * z + z ^ 2 / 2 + ri * z ^ 3 / 5 + z ^ 4 / 24 + z ^ 6 / 500)
    (hq : q * (2 + P) = P) :
    |q - (z * ri / 2 + z ^ 2 / 8)| ≤ z ^ 3 := by
  have hri1 : ri ≤ 71 / 100 := by nlinarith only [hri, hri0]
  have hP0 : 0 ≤ P := by nlinarith only [hP1, hz0, hri0]
  have h2P : 0 < 2 + P := by linarith
  set Y2 := z * ri / 2 + z ^ 2 / 8 with hY2
  have hzp3 : 0 < z ^ 3 := pow_pos hz0 3
  have hz4 : z ^ 4 ≤ z ^ 3 / 10 := by
    have : z ^ 4 = z ^ 3 * z := by ring
    rw [this]; nlinarith only [hz1, hzp3]
  have hz6 : z ^ 6 ≤ z ^ 3 / 1000 := by
    have : z ^ 6 = z ^ 3 * z ^ 3 := by ring
    have h3 : z ^ 3 ≤ 1 / 1000 := by
      have := pow_le_pow_left₀ hz0.le hz1 3
      norm_num at this ⊢; linarith
    rw [this]; nlinarith only [h3, hzp3]
  have hz5 : 0 < z ^ 5 := pow_pos hz0 5
  have hrz3 : 0 < ri * z ^ 3 := mul_pos hri0 hzp3
  have hrz3' : ri * z ^ 3 ≤ 71 / 100 * z ^ 3 := by nlinarith only [hri1, hzp3]
  have e1 : ri * ri * z ^ 2 = z ^ 2 / 2 := by rw [hri]; ring
  have hY2pos : 0 < Y2 := by rw [hY2]; positivity
  have hY2le : Y2 ≤ 1 / 10 := by
    rw [hY2]; nlinarith only [hz0, hz1, hri1, hri0]
  have hz3le : z ^ 3 ≤ 1 / 1000 := by
    have := pow_le_pow_left₀ hz0.le hz1 3
    norm_num at this ⊢; linarith
  have hqeq : q = P / (2 + P) := by field_simp; linarith
  have c1 : 0 ≤ 1 - Y2 + z ^ 3 := by linarith
  have c2 : 0 ≤ 1 - Y2 - z ^ 3 := by linarith
  rw [abs_le]
  constructor
  · have h1 := mul_nonneg (sub_nonneg.2 hP1) c1
    have : (Y2 - z ^ 3) * (2 + P) ≤ P := by
      rw [hY2] at h1 c1 ⊢
      nlinarith only [h1, e1, hrz3, hrz3', hz4, hz5, hzp3, hz1, hri0, hz0]
    have : Y2 - z ^ 3 ≤ q := by
      rw [hqeq, le_div_iff₀ h2P]; exact this
    linarith
  · have hP2' : P ≤ ri * z + z ^ 2 / 2 + z ^ 3 / 2 := by
      nlinarith only [hP2, hrz3', hz4, hz6, hzp3]
    have h1 := mul_nonneg (sub_nonneg.2 hP2') c2
    have e5 : ri * ri * ri * z ^ 3 = ri * z ^ 3 / 2 := by rw [mul_assoc ri ri ri, hri]; ring
    have : P ≤ (Y2 + z ^ 3) * (2 + P) := by
      rw [hY2] at h1 c2 ⊢
      nlinarith only [h1, e1, e5, hrz3, hrz3', hz4, hz5, hzp3, hz6, hz1, hri0, hz0]
    have : q ≤ Y2 + z ^ 3 := by
      rw [hqeq, div_le_iff₀ h2P]; linarith
    linarith

/-- Slit coordinate near the tip: if `cosh(π(ξ_*+r)) = √2 (1+y²)/(1-y²)`, `y ∈ (0,1)`, `π r ≤ 1/10`, then
`|y² - (π r/(2√2) + (π r)²/8)| ≤ (π r)³`. -/
lemma slit_sq_expansion {r y : ℝ} (hr : 0 < r) (hr1 : π * r ≤ 1 / 10) (hy0 : 0 < y) (hy1 : y < 1)
    (hxy : Real.cosh (π * (xiStar + r)) = √2 * (1 + y ^ 2) / (1 - y ^ 2)) :
    |y ^ 2 - (π * r / (2 * √2) + (π * r) ^ 2 / 8)| ≤ (π * r) ^ 3 := by
  have hpi := Real.pi_pos
  have hz0 : 0 < π * r := mul_pos hpi hr
  set z := π * r with hz
  have hz1' : z ≤ 1 := by linarith
  have hu : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hu0 : 0 < √2 := Real.sqrt_pos.mpr (by norm_num)
  have hy2 : 0 < 1 - y ^ 2 := by nlinarith only [hy0, hy1]
  set ri : ℝ := 1 / √2 with hri
  have hri2 : ri * ri = 1 / 2 := by rw [hri]; field_simp; nlinarith only [hu]
  have hri0 : 0 < ri := by positivity
  have hadd : Real.cosh (π * (xiStar + r)) = √2 * Real.cosh z + Real.sinh z := by
    rw [mul_add, Real.cosh_add, cosh_pi_xiStar, sinh_pi_mul_xiStar]; ring
  rw [hadd] at hxy
  have hA : Real.cosh z + ri * Real.sinh z = (1 + y ^ 2) / (1 - y ^ 2) := by
    rw [eq_div_iff hy2.ne']
    have h1 : (√2 * Real.cosh z + Real.sinh z) * (1 - y ^ 2) = √2 * (1 + y ^ 2) := by
      rw [hxy]; field_simp
    have h2 : (Real.cosh z + ri * Real.sinh z) * (1 - y ^ 2) * √2 = √2 * (1 + y ^ 2) := by
      rw [← h1, hri]; field_simp
    exact mul_right_cancel₀ hu0.ne' (by linarith only [h2])
  set P : ℝ := Real.cosh z - 1 + ri * Real.sinh z with hP
  have hq : y ^ 2 * (2 + P) = P := by
    have h1 : (1 + P) * (1 - y ^ 2) = 1 + y ^ 2 := by
      rw [show 1 + P = Real.cosh z + ri * Real.sinh z by rw [hP]; ring, hA]; field_simp
    nlinarith only [h1]
  obtain ⟨c1, c2⟩ := cosh_bounds hz0.le hz1'
  obtain ⟨s1, s2⟩ := sinh_bounds hz0.le hz1'
  have hP1 : ri * z + z ^ 2 / 2 ≤ P := by
    have : ri * z ≤ ri * Real.sinh z := mul_le_mul_of_nonneg_left s1 hri0.le
    have h4 : 0 ≤ z ^ 4 / 24 := by positivity
    rw [hP]; linarith only [this, c1, h4]
  have hP2 : P ≤ ri * z + z ^ 2 / 2 + ri * z ^ 3 / 5 + z ^ 4 / 24 + z ^ 6 / 500 := by
    have : ri * Real.sinh z ≤ ri * (z + z ^ 3 / 5) := mul_le_mul_of_nonneg_left s2 hri0.le
    rw [hP]; nlinarith only [this, c2]
  have := slit_core hz0 (by linarith) hri2 hri0 hP1 hP2 hq
  have e : z * ri / 2 = z / (2 * √2) := by rw [hri]; field_simp
  rw [e] at this
  exact this

lemma inv_cube_expansion {ε : ℝ} (hε : |ε| ≤ 1 / 2) :
    |1 / (1 + ε) ^ 3 - 1 + 3 * ε| ≤ 88 * ε ^ 2 := by
  have h1 : 1 / 2 ≤ 1 + ε := by linarith [(abs_le.mp hε).1]
  have h0 : 0 < 1 + ε := by linarith
  have e : 1 / (1 + ε) ^ 3 - 1 + 3 * ε = (6 * ε ^ 2 + 8 * ε ^ 3 + 3 * ε ^ 4) / (1 + ε) ^ 3 := by
    field_simp; ring
  rw [e]
  have hN0 : 0 ≤ 6 * ε ^ 2 + 8 * ε ^ 3 + 3 * ε ^ 4 := by
    have : 0 ≤ ε ^ 2 * (6 + 8 * ε + 3 * ε ^ 2) := by
      apply mul_nonneg (sq_nonneg _)
      nlinarith only [(abs_le.mp hε).1, sq_nonneg ε]
    nlinarith only [this]
  rw [abs_of_nonneg (by positivity), div_le_iff₀ (pow_pos h0 3)]
  have h3 : (1 / 2 : ℝ) ^ 3 ≤ (1 + ε) ^ 3 := pow_le_pow_left₀ (by norm_num) h1 3
  have hε3 : |ε ^ 3| ≤ ε ^ 2 / 2 := by
    rw [abs_pow]; calc |ε| ^ 3 = |ε| * ε ^ 2 := by rw [pow_succ, sq_abs]; ring
      _ ≤ 1 / 2 * ε ^ 2 := mul_le_mul_of_nonneg_right hε (sq_nonneg _)
      _ = ε ^ 2 / 2 := by ring
  have hε4 : ε ^ 4 ≤ ε ^ 2 / 4 := by
    have : ε ^ 2 ≤ 1 / 4 := by nlinarith only [(abs_le.mp hε), sq_abs ε, abs_nonneg ε]
    nlinarith only [this, sq_nonneg ε]
  have hN : 6 * ε ^ 2 + 8 * ε ^ 3 + 3 * ε ^ 4 ≤ 11 * ε ^ 2 := by
    have := (abs_le.mp hε3).2
    nlinarith only [this, hε4]
  calc 6 * ε ^ 2 + 8 * ε ^ 3 + 3 * ε ^ 4 ≤ 11 * ε ^ 2 := hN
    _ ≤ 88 * ε ^ 2 * (1 / 2) ^ 3 := by nlinarith only [sq_nonneg ε]
    _ ≤ 88 * ε ^ 2 * (1 + ε) ^ 3 := by gcongr

lemma core_expansion {τ f b Y : ℝ} (hτ0 : 0 < τ) (hτ1 : τ ≤ 1 / 1000)
    (hY1 : 1 ≤ Y) (hY2 : Y ≤ 6 / 5) (hb1 : 1 ≤ b) (hb2 : b ≤ 11 / 10)
    (hf : |f - 1 - b * τ| ≤ 270 * τ ^ 2) :
    |(1 - Y * τ * f) ^ 3 / (√f) ^ 3 - 1 + (3 * Y + 3 * b / 2) * τ| ≤ 500 * τ ^ 2 := by
  have hτ2 : τ ^ 2 ≤ τ / 1000 := by nlinarith only [hτ0, hτ1]
  have hτ3 : 270 * τ ^ 2 ≤ 27 / 100 * τ := by nlinarith only [hτ2]
  obtain ⟨hf1, hf2⟩ := abs_le.mp hf
  have hfm1 : |f - 1| ≤ 137 / 100 * τ := by
    rw [abs_le]; constructor <;> nlinarith only [hf1, hf2, hτ3, hb1, hb2, hτ0]
  have hf0 : 0 < f := by
    have := (abs_le.mp hfm1).1; nlinarith only [this, hτ1, hτ0]
  have hfm2 : (f - 1) ^ 2 ≤ (137 / 100 * τ) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hfm1 2
  set v := √f with hv
  have hsq := abs_sqrt_sub_le hf0.le
  rw [← hv] at hsq
  set ε := v - 1 with hε
  have hε1 : |ε - b * τ / 2| ≤ 136 * τ ^ 2 := by
    have h1 : |v - (1 + (f - 1) / 2)| ≤ (f - 1) ^ 2 / 2 := hsq
    have h2 : (f - 1) ^ 2 / 2 ≤ 94 / 100 * τ ^ 2 := by nlinarith only [hfm2]
    have h3 : |(f - 1) / 2 - b * τ / 2| ≤ 135 * τ ^ 2 := by
      have : (f - 1) / 2 - b * τ / 2 = (f - 1 - b * τ) / 2 := by ring
      rw [this, abs_div, abs_of_pos (two_pos : (0 : ℝ) < 2)]
      nlinarith only [hf]
    have : ε - b * τ / 2 = (v - (1 + (f - 1) / 2)) + ((f - 1) / 2 - b * τ / 2) := by rw [hε]; ring
    rw [this]
    calc _ ≤ |v - (1 + (f - 1) / 2)| + |(f - 1) / 2 - b * τ / 2| := abs_add_le _ _
      _ ≤ 136 * τ ^ 2 := by nlinarith only [h1, h2, h3]
  have hεb : |ε| ≤ 7 / 10 * τ := by
    have : |ε| ≤ |b * τ / 2| + |ε - b * τ / 2| := by
      calc |ε| = |b * τ / 2 + (ε - b * τ / 2)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    have h2 : |b * τ / 2| ≤ 11 / 20 * τ := by
      rw [abs_of_nonneg (by positivity)]; nlinarith only [hb2, hτ0]
    nlinarith only [this, h2, hε1, hτ2]
  have hε12 : |ε| ≤ 1 / 2 := by nlinarith only [hεb, hτ1, hτ0]
  have hinv := inv_cube_expansion hε12
  have hv1 : v = 1 + ε := by rw [hε]; ring
  rw [hv1]
  have hε2 : ε ^ 2 ≤ 49 / 100 * τ ^ 2 := by
    have : ε ^ 2 = |ε| ^ 2 := (sq_abs ε).symm
    rw [this]
    calc |ε| ^ 2 ≤ (7 / 10 * τ) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hεb 2
      _ = 49 / 100 * τ ^ 2 := by ring
  have hec : |1 / (1 + ε) ^ 3 - (1 - 3 * b * τ / 2)| ≤ 452 * τ ^ 2 := by
    have e : 1 / (1 + ε) ^ 3 - (1 - 3 * b * τ / 2) =
        (1 / (1 + ε) ^ 3 - 1 + 3 * ε) - 3 * (ε - b * τ / 2) := by ring
    rw [e]
    calc _ ≤ |1 / (1 + ε) ^ 3 - 1 + 3 * ε| + |3 * (ε - b * τ / 2)| := abs_sub _ _
      _ ≤ 88 * ε ^ 2 + 3 * (136 * τ ^ 2) := by
          rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
          exact add_le_add hinv (by nlinarith only [hε1])
      _ ≤ 452 * τ ^ 2 := by nlinarith only [hε2, hτ0]
  -- the cubic factor
  set q := Y * τ * f with hq
  have hw : |q - Y * τ| ≤ 165 / 100 * τ ^ 2 := by
    have : q - Y * τ = Y * τ * (f - 1) := by rw [hq]; ring
    rw [this, abs_mul, abs_of_pos (by positivity)]
    calc Y * τ * |f - 1| ≤ Y * τ * (137 / 100 * τ) := mul_le_mul_of_nonneg_left hfm1 (by positivity)
      _ ≤ 6 / 5 * τ * (137 / 100 * τ) := by gcongr
      _ ≤ 165 / 100 * τ ^ 2 := by nlinarith only [sq_nonneg τ]
  have hq0 : 0 ≤ q := by positivity
  have hqb : q ≤ 121 / 100 * τ := by
    have := (abs_le.mp hw).2
    nlinarith only [this, hY2, hτ0, hτ2]
  have hq2 : q ^ 2 ≤ (121 / 100) ^ 2 * τ ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hq0 hqb 2
  have hq3 : q ^ 3 ≤ τ ^ 2 / 100 := by
    have : q ^ 3 = q * q ^ 2 := by ring
    rw [this]
    have h1 : q * q ^ 2 ≤ (121 / 100 * τ) * ((121 / 100) ^ 2 * τ ^ 2) :=
      mul_le_mul hqb hq2 (sq_nonneg _) (by positivity)
    nlinarith only [h1, hτ0, hτ1, hτ2, pow_pos hτ0 3]
  have hcube : |(1 - q) ^ 3 - (1 - 3 * Y * τ)| ≤ 10 * τ ^ 2 := by
    have e : (1 - q) ^ 3 - (1 - 3 * Y * τ) = -3 * (q - Y * τ) + 3 * q ^ 2 - q ^ 3 := by ring
    rw [e, abs_le]
    have h1 := abs_le.mp hw
    constructor <;> nlinarith only [h1.1, h1.2, hq2, hq3, sq_nonneg q, pow_nonneg hq0 3, hτ0]
  -- product
  set A := (1 - q) ^ 3 with hA
  set Bv := 1 / (1 + ε) ^ 3 with hBv
  have hdiv : (1 - q) ^ 3 / (1 + ε) ^ 3 = A * Bv := by rw [hA, hBv]; ring
  rw [hdiv]
  obtain ⟨eA, hA'⟩ : ∃ eA, A = 1 - 3 * Y * τ + eA ∧ |eA| ≤ 10 * τ ^ 2 :=
    ⟨A - (1 - 3 * Y * τ), by ring, hcube⟩
  obtain ⟨eB, hB'⟩ : ∃ eB, Bv = 1 - 3 * b * τ / 2 + eB ∧ |eB| ≤ 452 * τ ^ 2 :=
    ⟨Bv - (1 - 3 * b * τ / 2), by ring, hec⟩
  rw [hA'.1, hB'.1]
  have e : (1 - 3 * Y * τ + eA) * (1 - 3 * b * τ / 2 + eB) - 1 + (3 * Y + 3 * b / 2) * τ =
      (9 * Y * b / 2) * τ ^ 2 + eA * (1 - 3 * b * τ / 2) + eB * (1 - 3 * Y * τ) + eA * eB := by ring
  rw [e]
  have b1 : |(9 * Y * b / 2) * τ ^ 2| ≤ 6 * τ ^ 2 := by
    rw [abs_of_nonneg (by positivity)]
    nlinarith only [hY2, hb2, hY1, hb1, sq_nonneg τ, mul_le_mul hY2 hb2 (by linarith) (by norm_num : (0 : ℝ) ≤ 6 / 5)]
  have c1 : |eA * (1 - 3 * b * τ / 2)| ≤ 11 * τ ^ 2 := by
    rw [abs_mul]
    have : |1 - 3 * b * τ / 2| ≤ 11 / 10 := by
      rw [abs_le]; constructor <;> nlinarith only [hb2, hb1, hτ0, hτ1]
    calc |eA| * |1 - 3 * b * τ / 2| ≤ 10 * τ ^ 2 * (11 / 10) :=
          mul_le_mul hA'.2 this (abs_nonneg _) (by positivity)
      _ = 11 * τ ^ 2 := by ring
  have c2 : |eB * (1 - 3 * Y * τ)| ≤ 453 * τ ^ 2 := by
    rw [abs_mul]
    have : |1 - 3 * Y * τ| ≤ 1002 / 1000 := by
      rw [abs_le]; constructor <;> nlinarith only [hY2, hY1, hτ0, hτ1]
    calc |eB| * |1 - 3 * Y * τ| ≤ 452 * τ ^ 2 * (1002 / 1000) :=
          mul_le_mul hB'.2 this (abs_nonneg _) (by positivity)
      _ ≤ 453 * τ ^ 2 := by nlinarith only [sq_nonneg τ]
  have c3 : |eA * eB| ≤ τ ^ 2 := by
    rw [abs_mul]
    calc |eA| * |eB| ≤ 10 * τ ^ 2 * (452 * τ ^ 2) :=
          mul_le_mul hA'.2 hB'.2 (abs_nonneg _) (by positivity)
      _ ≤ τ ^ 2 := by nlinarith only [hτ2, hτ0, sq_nonneg τ, pow_pos hτ0 3, hτ1]
  calc _ ≤ |(9 * Y * b / 2) * τ ^ 2| + |eA * (1 - 3 * b * τ / 2)| + |eB * (1 - 3 * Y * τ)| +
        |eA * eB| := by
        refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add_left
          (abs_add_le _ _) _)) le_rfl) |>.trans ?_
        exact le_rfl
    _ ≤ 500 * τ ^ 2 := by nlinarith only [b1, c1, c2, c3]

/-- `Y = π/(2√2)`, `b = 7π/(15√2) = Y - π/(30√2)`. -/
noncomputable def slitY : ℝ := π / (2 * √2)
noncomputable def slitB : ℝ := 7 * π / (15 * √2)

lemma slit_numerics : 11 / 10 ≤ slitY ∧ slitY ≤ 6 / 5 ∧ 1 ≤ slitB ∧ slitB ≤ 11 / 10 ∧
    slitB = slitY - π / (30 * √2) := by
  have hu : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hu0 : 0 < √2 := Real.sqrt_pos.mpr (by norm_num)
  have h1 : 7 / 5 ≤ √2 := by nlinarith only [hu, hu0]
  have h2 : √2 ≤ 142 / 100 := by nlinarith only [hu, hu0]
  have hp1 := Real.pi_gt_d2
  have hp2 := Real.pi_lt_d2
  unfold slitY slitB
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ (by positivity)]; nlinarith only [h2, hp1]
  · rw [div_le_iff₀ (by positivity)]; nlinarith only [h1, hp2]
  · rw [le_div_iff₀ (by positivity)]; nlinarith only [h2, hp1]
  · rw [div_le_iff₀ (by positivity)]; nlinarith only [h1, hp2]
  · field_simp; ring

/-- `k_tip = 32 (√Y)³/(9π²)` (closed form behind `pm:tip-match`). -/
lemma kTip_eq_slit : kTip = 32 * (√slitY) ^ 3 / (9 * π ^ 2) := by
  have hpi := Real.pi_pos
  have hu : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hu0 : 0 < √2 := Real.sqrt_pos.mpr (by norm_num)
  have hk := kTip_pos
  have hY0 : 0 < slitY := by unfold slitY; positivity
  have hR : 0 < 32 * (√slitY) ^ 3 / (9 * π ^ 2) := by
    have := Real.sqrt_pos.mpr hY0; positivity
  rw [← sq_eq_sq₀ hk.le hR.le]
  have h2 : (2 : ℝ) ^ (3 / 4 : ℝ) = √(2 * √2) := by
    rw [Real.sqrt_eq_rpow, show (2 * √2 : ℝ) = (2 : ℝ) ^ (3 / 2 : ℝ) by
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add two_pos, Real.rpow_one,
        Real.sqrt_eq_rpow], ← Real.rpow_mul (by norm_num)]
    norm_num
  have hk2 : kTip ^ 2 = 16 * (2 * √2) / (81 * π) := by
    unfold kTip
    rw [h2, div_pow, mul_pow, Real.sq_sqrt (by positivity), mul_pow, Real.sq_sqrt hpi.le]
    field_simp
    ring
  have hY3 : slitY ^ 3 = π ^ 3 / (16 * √2) := by
    unfold slitY; field_simp; nlinarith only [hu]
  rw [hk2, div_pow, mul_pow, ← pow_mul, show 3 * 2 = 2 * 3 by norm_num, pow_mul, Real.sq_sqrt hY0.le,
    hY3]
  field_simp
  nlinarith only [hu, hu0]

/-- The slit coordinate in the Langer phase: `|y² - Yτ(1 + bτ)| ≤ 290 τ³`, `τ = τ(ξ_* + r)`. -/
lemma slit_sq_tau {r y : ℝ} (hr : 0 < r) (hr1 : π * r ≤ 1 / 10) (hy0 : 0 < y) (hy1 : y < 1)
    (hxy : Real.cosh (π * (xiStar + r)) = √2 * (1 + y ^ 2) / (1 - y ^ 2)) :
    |y ^ 2 - slitY * tauPhase (xiStar + r) * (1 + slitB * tauPhase (xiStar + r))| ≤
      290 * tauPhase (xiStar + r) ^ 3 := by
  have hpi := Real.pi_pos
  have hp1 := Real.pi_gt_d2
  have hp2 := Real.pi_lt_d2
  have hr30 : r ≤ 1 / 30 := by nlinarith only [hr1, Real.pi_gt_three, hr]
  have hτ := tau_tip_expansion hr hr1
  obtain ⟨η0, η1⟩ := eta_bounds
  set τ := tauPhase (xiStar + r) with hτdef
  have hτ' : |τ - r - π / (30 * √2) * r ^ 2| ≤ 2 * r ^ 3 := hτ
  obtain ⟨hr2τ, hτ2r, hinv, hsq⟩ := inversion_aux hr hr30 η0 η1 hτ'
  have hτ0 : 0 < τ := tauPhase_pos (by linarith)
  obtain ⟨hY1, hY2, -, -, hbY⟩ := slit_numerics
  have hS2 := slit_sq_expansion hr hr1 hy0 hy1 hxy
  set η := π / (30 * √2) with hη
  have hu : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hu0 : 0 < √2 := Real.sqrt_pos.mpr (by norm_num)
  have hYr : π * r / (2 * √2) = slitY * r := by unfold slitY; ring
  have hYr2 : (π * r) ^ 2 / 8 = slitY ^ 2 * r ^ 2 := by
    unfold slitY; field_simp; nlinarith only [hu]
  rw [hYr, hYr2] at hS2
  have hz3 : (π * r) ^ 3 ≤ 8 * 3.15 ^ 3 * τ ^ 3 := by
    have h1 : π * r ≤ 3.15 * (2 * τ) := by nlinarith only [hp2, hr2τ, hr, hpi]
    have h2 : (π * r) ^ 3 ≤ (3.15 * (2 * τ)) ^ 3 :=
      pow_le_pow_left₀ (by positivity) h1 3
    calc (π * r) ^ 3 ≤ (3.15 * (2 * τ)) ^ 3 := h2
      _ = 8 * 3.15 ^ 3 * τ ^ 3 := by ring
  have key : y ^ 2 - slitY * τ * (1 + slitB * τ) =
      (y ^ 2 - (slitY * r + slitY ^ 2 * r ^ 2)) + slitY * (r - (τ - η * τ ^ 2)) +
        slitY ^ 2 * (r ^ 2 - τ ^ 2) := by
    rw [hbY]; ring
  rw [key]
  have b1 : |slitY * (r - (τ - η * τ ^ 2))| ≤ slitY * (24 * τ ^ 3) := by
    rw [abs_mul, abs_of_pos (by linarith)]
    exact mul_le_mul_of_nonneg_left hinv (by linarith)
  have b2 : |slitY ^ 2 * (r ^ 2 - τ ^ 2)| ≤ slitY ^ 2 * (2 * τ ^ 3) := by
    rw [abs_mul, abs_of_pos (by positivity)]
    exact mul_le_mul_of_nonneg_left hsq (by positivity)
  have hτ3 : 0 < τ ^ 3 := pow_pos hτ0 3
  calc _ ≤ |y ^ 2 - (slitY * r + slitY ^ 2 * r ^ 2)| + |slitY * (r - (τ - η * τ ^ 2))| +
        |slitY ^ 2 * (r ^ 2 - τ ^ 2)| := (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ (π * r) ^ 3 + slitY * (24 * τ ^ 3) + slitY ^ 2 * (2 * τ ^ 3) := by
        gcongr
    _ ≤ 290 * τ ^ 3 := by
        have hY2' : slitY ^ 2 ≤ 36 / 25 := by nlinarith only [hY1, hY2]
        nlinarith only [hz3, hY2, hY2', hτ3, mul_le_mul_of_nonneg_right hY2 hτ3.le,
          mul_le_mul_of_nonneg_right hY2' hτ3.le]

/-- **Core of `pm:tip-match`**: for the slit coordinate `y = y(x)` at phase `τ = τ(x) ≤ 10⁻³`,
`|(3 k_tip/16) (1-y²)³/(3y³) - (2/(9π²)) τ^{-3/2} + (11√2/(45π)) τ^{-1/2}| ≤ 500 (2/(9π²)) τ^{1/2}`
(here `(1-y²)³/(3y³) = 1/(3y³) - 1/y + y - y³/3`). -/
theorem slit_expansion_core {x y : ℝ} (hx : xiStar < x) (hxr : π * (x - xiStar) ≤ 1 / 10)
    (hτ1 : tauPhase x ≤ 1 / 1000) (hy0 : 0 < y) (hy1 : y < 1)
    (hxy : Real.cosh (π * x) = √2 * (1 + y ^ 2) / (1 - y ^ 2)) :
    |3 * kTip / 16 * ((1 - y ^ 2) ^ 3 / (3 * y ^ 3)) - 2 / (9 * π ^ 2) / (√(tauPhase x)) ^ 3 +
        11 * √2 / (45 * π) / √(tauPhase x)| ≤ 500 * (2 / (9 * π ^ 2)) * √(tauPhase x) := by
  have hpi := Real.pi_pos
  obtain ⟨r, hr, rfl⟩ : ∃ r, 0 < r ∧ x = xiStar + r := ⟨x - xiStar, sub_pos.mpr hx, by ring⟩
  have hr1 : π * r ≤ 1 / 10 := by simpa using hxr
  set τ := tauPhase (xiStar + r) with hτdef
  have hτ0 : 0 < τ := tauPhase_pos (by linarith)
  obtain ⟨hY1, hY2, hb1, hb2, -⟩ := slit_numerics
  have hY0 : 0 < slitY := by linarith
  have hS := slit_sq_tau hr hr1 hy0 hy1 (by simpa using hxy)
  set f := y ^ 2 / (slitY * τ) with hf
  have hYτ : 0 < slitY * τ := mul_pos hY0 hτ0
  have hq : y ^ 2 = slitY * τ * f := by rw [hf]; field_simp
  have hfb : |f - 1 - slitB * τ| ≤ 270 * τ ^ 2 := by
    have e : f - 1 - slitB * τ = (y ^ 2 - slitY * τ * (1 + slitB * τ)) / (slitY * τ) := by
      rw [hf]; field_simp; ring
    rw [e, abs_div, abs_of_pos hYτ, div_le_iff₀ hYτ]
    calc _ ≤ 290 * τ ^ 3 := hS
      _ ≤ 270 * τ ^ 2 * (slitY * τ) := by
          have : 0 ≤ τ ^ 3 := by positivity
          nlinarith only [hY1, this, hτ0, pow_pos hτ0 3]
  have hcore := core_expansion hτ0 hτ1 (by linarith) hY2 hb1 hb2 hfb
  have hf0 : 0 < f := by rw [hf]; positivity
  set s := √τ with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hτ0
  have hss : s ^ 2 = τ := Real.sq_sqrt hτ0.le
  set Ys := √slitY with hYs
  have hYs0 : 0 < Ys := Real.sqrt_pos.mpr hY0
  set v := √f with hv
  have hv0 : 0 < v := Real.sqrt_pos.mpr hf0
  have hy : y = Ys * s * v := by
    have : y = √(y ^ 2) := (Real.sqrt_sq hy0.le).symm
    rw [this, hq, Real.sqrt_mul (by positivity), Real.sqrt_mul hY0.le]
  have hkT := kTip_eq_slit
  rw [← hYs] at hkT
  have hκ : 3 * slitY + 3 * slitB / 2 = 11 * π / (5 * √2) := by
    unfold slitY slitB; field_simp; ring
  rw [hκ] at hcore
  set e := (1 - slitY * τ * f) ^ 3 / v ^ 3 - 1 + 11 * π / (5 * √2) * τ with he
  have hMk : 11 * √2 / (45 * π) = 2 / (9 * π ^ 2) * (11 * π / (5 * √2)) := by
    have hu : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hu0 : 0 < √2 := Real.sqrt_pos.mpr (by norm_num)
    field_simp
    nlinarith only [hu]
  have hE : 3 * kTip / 16 * ((1 - y ^ 2) ^ 3 / (3 * y ^ 3)) - 2 / (9 * π ^ 2) / s ^ 3 +
      11 * √2 / (45 * π) / s = 2 / (9 * π ^ 2) / s ^ 3 * e := by
    have h1 : (1 - y ^ 2) ^ 3 / (3 * y ^ 3) = (1 - slitY * τ * f) ^ 3 / (3 * (Ys * s * v) ^ 3) := by
      rw [← hq, ← hy]
    rw [h1, hMk, hkT, he, ← hss]
    field_simp
    ring
  rw [hE, abs_mul, abs_of_pos (by positivity)]
  have hM : 0 < 2 / (9 * π ^ 2) := by positivity
  calc 2 / (9 * π ^ 2) / s ^ 3 * |e| ≤ 2 / (9 * π ^ 2) / s ^ 3 * (500 * τ ^ 2) :=
        mul_le_mul_of_nonneg_left hcore (by positivity)
    _ = 500 * (2 / (9 * π ^ 2)) * s := by
        rw [← hss]; field_simp

/-- `κ_comb = (3π/2)^{2/3}`, the Airy-phase scale of the comb (`cts:upper-design`). -/
noncomputable def kappaComb : ℝ := (3 * π / 2) ^ (2 / 3 : ℝ)

lemma kappaComb_pos : 0 < kappaComb := by unfold kappaComb; have := Real.pi_pos; positivity

/-- `κ_comb^{3/2} = 3π/2`. -/
lemma kappaComb_rpow : kappaComb ^ (3 / 2 : ℝ) = 3 * π / 2 := by
  unfold kappaComb
  rw [← Real.rpow_mul (by have := Real.pi_pos; positivity)]; norm_num

/-- `κ_comb √κ_comb = 3π/2`. -/
lemma kappaComb_mul_sqrt : kappaComb * √kappaComb = 3 * π / 2 := by
  rw [← kappaComb_rpow, Real.sqrt_eq_rpow, ← Real.rpow_one_add' kappaComb_pos.le (by norm_num)]
  norm_num

/-- The scale `λ = (k_tip c')^{-2/3}`. -/
noncomputable def tipLam (c : ℝ) : ℝ := (kTip * c) ^ (-(2 / 3) : ℝ)

lemma rpow_neg_three_half_eq_inv_sqrt_cube {t : ℝ} (ht : 0 < t) : t ^ (-(3 / 2) : ℝ) = 1 / √t ^ 3 := by
  rw [Real.rpow_neg ht.le, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ht.le]
  norm_num

lemma rpow_neg_half_eq_inv_sqrt {t : ℝ} (ht : 0 < t) : t ^ (-(1 / 2) : ℝ) = 1 / √t := by
  rw [Real.rpow_neg ht.le, Real.sqrt_eq_rpow]; simp

lemma sqrt_tipLam_cube {c : ℝ} (hc : 0 < c) : √(tipLam c) ^ 3 = (kTip * c)⁻¹ := by
  have hk := kTip_pos
  have ha : 0 < kTip * c := by positivity
  unfold tipLam
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul ha.le, ← Real.rpow_natCast, ← Real.rpow_mul ha.le]
  have : (-(2 / 3 : ℝ)) * (1 / 2) * ((3 : ℕ) : ℝ) = -1 := by norm_num
  rw [this, Real.rpow_neg_one]


lemma bc_coeff {κ K a lam : ℝ} (hK : 0 < K) (hκK : κ * K = 3 * π / 2) :
    -(7 * π * a) / (15 * √2 * κ) * lam / (π * K) +
      -(4 * π) / (15 * √2) * a * lam / (π * (3 * π / 2)) = -(11 * √2 / (45 * π)) * a * lam := by
  have hpi := Real.pi_pos
  have hu : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hu0 : 0 < √2 := Real.sqrt_pos.mpr (by norm_num)
  have hκ : κ = 3 * π / 2 / K := by field_simp; linarith
  rw [hκ]
  field_simp
  rw [hu]
  ring

/-- **`pm:tip-match`** (Lemma C14$_0$, renormalized tip-dipole boundary cancellation): with `λ = (k_tip c')^{-2/3}`,
`x` the point at Langer phase `τ(x) = λ S` and `y = y(x)` the slit coordinate (`cosh πx = √2 (1+y²)/(1-y²)`),
`𝒯(S) = (3|a_1|/(16 c'))(1/(3y³) - 1/y + y - y³/3)` satisfies
`𝒯(S) - |a_1|/(3π κ^{3/2}) S^{-3/2} - c_Sm^{(0)} λ/(π√κ) S^{-1/2} - g_{1,geo}^{(0)}|a_1| λ/(π κ^{3/2}) S^{-1/2}
 = O(c'^{-1} (λ S)^{1/2})`,
`c_Sm^{(0)} = -7π|a_1|/(15√2 κ)`, `g_{1,geo}^{(0)} = -4π/(15√2)`. -/
theorem tip_match :
    ∃ C τ₀ : ℝ, 0 < τ₀ ∧ ∀ c S : ℝ, 0 < c → 0 < S → ∀ x y : ℝ, xiStar < x → 0 < y → y < 1 →
      Real.cosh (π * x) = √2 * (1 + y ^ 2) / (1 - y ^ 2) →
      tauPhase x = tipLam c * S → tipLam c * S ≤ τ₀ →
      |3 * |airyZero 1| / (16 * c) * (1 / (3 * y ^ 3) - 1 / y + y - y ^ 3 / 3) -
          |airyZero 1| / (3 * π * kappaComb ^ (3 / 2 : ℝ)) * S ^ (-(3 / 2) : ℝ) -
          (-(7 * π * |airyZero 1|) / (15 * √2 * kappaComb) * tipLam c / (π * √kappaComb)) *
            S ^ (-(1 / 2) : ℝ) -
          (-(4 * π) / (15 * √2) * |airyZero 1| * tipLam c / (π * kappaComb ^ (3 / 2 : ℝ))) *
            S ^ (-(1 / 2) : ℝ)| ≤
        C * c ^ (-1 : ℝ) * (tipLam c * S) ^ (1 / 2 : ℝ) := by
  have hpi := Real.pi_pos
  have hk := kTip_pos
  set ε₁ := tauPhase (xiStar + 1 / (10 * π)) with hε₁
  have hpos1 : 0 < 1 / (10 * π) := by positivity
  have hε₁0 : 0 < ε₁ := tauPhase_pos (by linarith)
  refine ⟨500 * (2 / (9 * π ^ 2)) * |airyZero 1| / kTip, min (1 / 1000) (ε₁ / 2),
    lt_min (by norm_num) (by positivity), fun c S hc hS x y hx hy0 hy1 hxy hτ hτ0 => ?_⟩
  have hτ1 : tauPhase x ≤ 1 / 1000 := hτ ▸ hτ0.trans (min_le_left _ _)
  have hτε : tauPhase x < ε₁ := by
    have := hτ ▸ hτ0.trans (min_le_right _ _); linarith
  have hxr := le_of_tauPhase_lt hx hτε
  have hcore := slit_expansion_core hx hxr hτ1 hy0 hy1 hxy
  set lam := tipLam c with hlam
  have hlam0 : 0 < lam := by rw [hlam]; unfold tipLam; positivity
  set sl := √lam with hsl
  set sS := √S with hsS
  have hsl0 : 0 < sl := Real.sqrt_pos.mpr hlam0
  have hsS0 : 0 < sS := Real.sqrt_pos.mpr hS
  have hτsq : √(tauPhase x) = sl * sS := by
    rw [hτ, Real.sqrt_mul hlam0.le]
  rw [hτsq] at hcore
  have hsl3 : sl ^ 3 = (kTip * c)⁻¹ := sqrt_tipLam_cube hc
  have hc1 : c ^ (-1 : ℝ) = kTip * sl ^ 3 := by
    rw [Real.rpow_neg_one, hsl3]; field_simp
  have hlam2 : lam = sl ^ 2 := (Real.sq_sqrt hlam0.le).symm
  have hκ := kappaComb_rpow
  have hκs := kappaComb_mul_sqrt
  have hκ0 := kappaComb_pos
  have hsκ : 0 < √kappaComb := Real.sqrt_pos.mpr hκ0
  have hu : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hu0 : 0 < √2 := Real.sqrt_pos.mpr (by norm_num)
  rw [rpow_neg_three_half_eq_inv_sqrt_cube hS, rpow_neg_half_eq_inv_sqrt hS, hκ, hc1, ← Real.sqrt_eq_rpow,
    Real.sqrt_mul hlam0.le]
  have hΦ : 1 / (3 * y ^ 3) - 1 / y + y - y ^ 3 / 3 = (1 - y ^ 2) ^ 3 / (3 * y ^ 3) := by
    field_simp; ring
  rw [hΦ]
  have ha1 : 0 < |airyZero 1| := abs_pos.mpr (airyZero_neg 1).ne
  have hc2 : 1 / c = kTip * sl ^ 3 := by rw [hsl3]; field_simp
  have hBC := bc_coeff (a := |airyZero 1|) (lam := lam) hsκ hκs
  have hident : 3 * |airyZero 1| / (16 * c) * ((1 - y ^ 2) ^ 3 / (3 * y ^ 3)) -
      |airyZero 1| / (3 * π * (3 * π / 2)) * (1 / sS ^ 3) -
      (-(7 * π * |airyZero 1|) / (15 * √2 * kappaComb) * lam / (π * √kappaComb)) * (1 / sS) -
      (-(4 * π) / (15 * √2) * |airyZero 1| * lam / (π * (3 * π / 2))) * (1 / sS) =
      |airyZero 1| * sl ^ 3 * (3 * kTip / 16 * ((1 - y ^ 2) ^ 3 / (3 * y ^ 3)) -
        2 / (9 * π ^ 2) / (sl * sS) ^ 3 + 11 * √2 / (45 * π) / (sl * sS)) := by
    have e1 : 3 * |airyZero 1| / (16 * c) = 3 * |airyZero 1| / 16 * (kTip * sl ^ 3) := by
      rw [← hc2]; field_simp
    have e2 : -(7 * π * |airyZero 1|) / (15 * √2 * kappaComb) * lam / (π * √kappaComb) * (1 / sS) +
        -(4 * π) / (15 * √2) * |airyZero 1| * lam / (π * (3 * π / 2)) * (1 / sS) =
        -(11 * √2 / (45 * π)) * |airyZero 1| * lam * (1 / sS) := by
      rw [← add_mul, hBC]
    have e3 : ∀ A B C D : ℝ, A - B - C - D = A - B - (C + D) := fun A B C D => by ring
    rw [e3, e2, e1, hlam2]
    field_simp
    ring
  rw [hident, abs_mul, abs_of_pos (by positivity)]
  have hM : 0 < 2 / (9 * π ^ 2) := by positivity
  calc |airyZero 1| * sl ^ 3 * |3 * kTip / 16 * ((1 - y ^ 2) ^ 3 / (3 * y ^ 3)) -
        2 / (9 * π ^ 2) / (sl * sS) ^ 3 + 11 * √2 / (45 * π) / (sl * sS)| ≤
      |airyZero 1| * sl ^ 3 * (500 * (2 / (9 * π ^ 2)) * (sl * sS)) :=
        mul_le_mul_of_nonneg_left hcore (by positivity)
    _ = 500 * (2 / (9 * π ^ 2)) * |airyZero 1| / kTip * (kTip * sl ^ 3) * (sl * sS) := by
        field_simp
    _ = _ := by ring

end FormalResearch.ModularBootstrap.FiveTerm

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.slit_expansion_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.slit_expansion_core

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.tip_match' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.tip_match
