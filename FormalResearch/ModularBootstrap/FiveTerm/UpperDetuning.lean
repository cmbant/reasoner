module

public import FormalResearch.ModularBootstrap.FiveTerm.UpperSmoothEnv
public import FormalResearch.ModularBootstrap.FiveTerm.Langer

/-!
# Detuning and edge ratio of the smoothed minimiser (FIVE-U; `cts:smooth-env` (3), algebraic half)

Source: `CFT/modular_bootstrap/paper/constant_term_slit_strip.tex`, Lemma C10 (`cts:smooth-env`), item (3),
the quantities `R_δ(y)`, `D_δ(y)` (`cts:Rdelta`).

For `F_δ = m_δ F_*` (`fDelta`) and `y ∈ (0,1)`, the pair-detuning identity of the exact comb gives
`K(y) F_*(e^{-iψ}) = q(y) F_*(iy)` with `q = 4y²/(1+y²)²` (`fStar_edge_eq`, generic in the outer datum), so

* `|K F_δ(e^{-iψ})| = R_δ |F_δ(iy)|` and `|F_δ(iy) + K F_δ(e^{-iψ})| = D_δ |F_δ(iy)|`
  (`fDelta_edge_ratio`), with the explicit `R_δ = q ‖m_δ(e^{-iψ})‖/‖m_δ(iy)‖`, `D_δ = ‖u + q v‖/‖u‖`;
* for `0 < δ ≤ 1/4`: `1 < D_δ ≤ 1 + R_δ`, `R_δ/10 ≤ D_δ - 1`, `D_δ ≤ 1 + √2`
  (`detuneD_bounds`), and `(9/16) y^{10}/(δ+y)² ≤ R_δ⁴ ≤ 2048 y^{10}/(δ+y)²` (`detuneR_pow4_bounds`);
* `1 + √2 < cosh(π/2)` (`one_add_sqrt_two_lt_cosh`), used for the range of the pair height.

All statements are exact and proved (no numerical input). Not here: the `x`-derivative bounds of
`cts:smooth-env` (3) and the strip factorisation (2); see `FIVEU_DESIGN.md`.
-/

@[expose] public section

open Complex Set
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm

lemma norm_sq_eq_re_im (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; ring

/-- `‖m_δ(iy)‖⁴ = (1+y²)/(1+(1-δ)²y²)`. -/
lemma norm_mEps_slit_pow4 {y δ : ℝ} (hy0 : 0 < y) (hy1 : y < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ‖mEps δ (Complex.I * (y : ℂ))‖ ^ 4 = (1 + y ^ 2) / (1 + (1 - δ) ^ 2 * y ^ 2) := by
  have hsq := mEps_slit_sq hy0 hy1 hδ0 hδ1
  have h4 : ‖mEps δ (Complex.I * (y : ℂ))‖ ^ 4 = ‖mEps δ (Complex.I * (y : ℂ)) ^ 2‖ ^ 2 := by
    rw [norm_pow]; ring
  rw [h4, norm_sq_eq_re_im, hsq]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, zero_add]
  have hA : (1 + (1 - δ) ^ 2 * y ^ 2) ≠ 0 := by positivity
  field_simp
  ring

/-- `‖m_δ(e^{-iψ})‖⁴ = 4y²/(δ² + (2-δ)²y²)`. -/
lemma norm_mEps_arc_pow4 {y δ : ℝ} (hy0 : 0 < y) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ‖mEps δ (starRingEnd ℂ (wPt y))‖ ^ 4 = 4 * y ^ 2 / (δ ^ 2 + (2 - δ) ^ 2 * y ^ 2) := by
  have hsq := mEps_arc_sq hy0 hδ0 hδ1
  have h4 : ‖mEps δ (starRingEnd ℂ (wPt y))‖ ^ 4 = ‖mEps δ (starRingEnd ℂ (wPt y)) ^ 2‖ ^ 2 := by
    rw [norm_pow]; ring
  rw [h4, norm_sq_eq_re_im, hsq]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, zero_add]
  have hD : (δ ^ 2 + (2 - δ) ^ 2 * y ^ 2) ≠ 0 := by positivity
  field_simp
  ring

/-- `q(y) = 4y²/(1+y²)²`. -/
noncomputable def qSlit (y : ℝ) : ℝ := 4 * y ^ 2 / (1 + y ^ 2) ^ 2

/-- The edge ratio `R_δ = q(y) |m_δ(e^{-iψ})/m_δ(iy)|` (`cts:Rdelta`). -/
noncomputable def detuneR (δ y : ℝ) : ℝ :=
  qSlit y * ‖mEps δ (starRingEnd ℂ (wPt y))‖ / ‖mEps δ (Complex.I * (y : ℂ))‖

/-- The exact phase-locked detuning `D_δ = |1 + R_δ e^{iΔφ_δ}| = |m_δ(iy) + q m_δ(e^{-iψ})|/|m_δ(iy)|`
(`cts:Rdelta`). -/
noncomputable def detuneD (δ y : ℝ) : ℝ :=
  ‖mEps δ (Complex.I * (y : ℂ)) + (qSlit y : ℂ) * mEps δ (starRingEnd ℂ (wPt y))‖ /
    ‖mEps δ (Complex.I * (y : ℂ))‖

lemma qSlit_bounds {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) : y ^ 2 ≤ qSlit y ∧ qSlit y ≤ 1 ∧ qSlit y ≤ 4 * y ^ 2 := by
  unfold qSlit
  have h1 : 0 < (1 + y ^ 2) ^ 2 := by positivity
  refine ⟨?_, ?_, ?_⟩
  · have hy2 : y ^ 2 < 1 := by nlinarith only [hy0, hy1]
    have h4 : (1 + y ^ 2) ^ 2 ≤ 4 := by nlinarith only [hy2, sq_nonneg y]
    rw [le_div_iff₀ h1]
    nlinarith only [mul_le_mul_of_nonneg_left h4 (sq_nonneg y)]
  · rw [div_le_one h1]; nlinarith only [sq_nonneg (1 - y ^ 2)]
  · rw [div_le_iff₀ h1]; nlinarith only [sq_nonneg y, mul_nonneg (sq_nonneg y) (sq_nonneg y)]

lemma one_le_norm_mEps_slit {y δ : ℝ} (hy0 : 0 < y) (hy1 : y < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    1 ≤ ‖mEps δ (Complex.I * (y : ℂ))‖ := by
  have h4 := norm_mEps_slit_pow4 hy0 hy1 hδ0 hδ1
  have hA : 0 < 1 + (1 - δ) ^ 2 * y ^ 2 := by positivity
  have h1 : 1 ≤ ‖mEps δ (Complex.I * (y : ℂ))‖ ^ 4 := by
    rw [h4, le_div_iff₀ hA]
    nlinarith only [sq_nonneg y, mul_nonneg (mul_nonneg hδ0.le (by linarith : (0 : ℝ) ≤ 2 - δ)) (sq_nonneg y)]
  by_contra hcon
  push Not at hcon
  have := pow_lt_one₀ (norm_nonneg _) hcon (by norm_num : (4 : ℕ) ≠ 0)
  linarith

lemma norm_mEps_arc_sq_le {y δ : ℝ} (hy0 : 0 < y) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ‖mEps δ (starRingEnd ℂ (wPt y))‖ ^ 2 ≤ 2 := by
  have h4 := norm_mEps_arc_pow4 hy0 hδ0 hδ1
  have hD : 0 < δ ^ 2 + (2 - δ) ^ 2 * y ^ 2 := by positivity
  have h1 : ‖mEps δ (starRingEnd ℂ (wPt y))‖ ^ 4 ≤ 4 := by
    rw [h4, div_le_iff₀ hD]
    nlinarith only [sq_nonneg y, mul_nonneg (sq_nonneg δ) (sq_nonneg δ), sq_nonneg δ,
      mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - δ) (by linarith : (0 : ℝ) ≤ 3 - δ)) (sq_nonneg y)]
  nlinarith only [h1, sq_nonneg (‖mEps δ (starRingEnd ℂ (wPt y))‖ ^ 2 - 2),
    sq_nonneg (‖mEps δ (starRingEnd ℂ (wPt y))‖ ^ 2), norm_nonneg (mEps δ (starRingEnd ℂ (wPt y)))]

/-- `R_δ ≤ √2` and `‖m_δ(iy)‖ ≥ 1`. -/
lemma detuneR_le {y δ : ℝ} (hy0 : 0 < y) (hy1 : y < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    detuneR δ y ≤ √2 := by
  unfold detuneR
  obtain ⟨-, hq1, -⟩ := qSlit_bounds hy0 hy1
  have hu := one_le_norm_mEps_slit hy0 hy1 hδ0 hδ1
  have hv := norm_mEps_arc_sq_le hy0 hδ0 hδ1
  have hv' : ‖mEps δ (starRingEnd ℂ (wPt y))‖ ≤ √2 := by
    rw [← Real.sqrt_sq (norm_nonneg _)]
    exact Real.sqrt_le_sqrt hv
  have hq0 : 0 ≤ qSlit y := (by positivity : 0 ≤ y ^ 2).trans (qSlit_bounds hy0 hy1).1
  rw [div_le_iff₀ (by linarith)]
  calc qSlit y * ‖mEps δ (starRingEnd ℂ (wPt y))‖ ≤ 1 * √2 :=
        mul_le_mul hq1 hv' (norm_nonneg _) zero_le_one
    _ ≤ √2 * ‖mEps δ (Complex.I * (y : ℂ))‖ := by nlinarith only [hu, Real.sqrt_nonneg 2]

lemma le_of_sq_le' {a b : ℝ} (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  by_contra hcon
  push Not at hcon
  nlinarith only [hcon, hb, h]

/-- `D_δ` versus `R_δ` (`cts:smooth-env` (3)): `1 < D_δ ≤ 1 + R_δ`, `D_δ - 1 ≥ R_δ/10`, `D_δ ≤ 1 + √2`
(for `0 < δ ≤ 1/4`, `y ∈ (0,1)`). -/
theorem detuneD_bounds {y δ : ℝ} (hy0 : 0 < y) (hy1 : y < 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 4) :
    1 < detuneD δ y ∧ detuneD δ y ≤ 1 + detuneR δ y ∧ detuneR δ y / 10 ≤ detuneD δ y - 1 ∧
      detuneD δ y ≤ 1 + √2 := by
  have hδ1' : δ < 1 := by linarith
  obtain ⟨a1, a2, a3⟩ := slit_facts hy0 hy1 hδ0 hδ1'
  obtain ⟨b1, b2, -⟩ := arc_facts hy0 hδ0 hδ1'
  obtain ⟨hq0', hq1, -⟩ := qSlit_bounds hy0 hy1
  have hq0 : 0 < qSlit y := lt_of_lt_of_le (by positivity) hq0'
  set u := mEps δ (Complex.I * (y : ℂ)) with hu
  set v := mEps δ (starRingEnd ℂ (wPt y)) with hv
  set q := qSlit y with hq
  have hu1 : 1 ≤ ‖u‖ := one_le_norm_mEps_slit hy0 hy1 hδ0 hδ1'
  have hu0 : 0 < ‖u‖ := by linarith
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr (fun h => by rw [h] at b1; simp at b1)
  have hRle := detuneR_le hy0 hy1 hδ0 hδ1'
  have hR : detuneR δ y = q * ‖v‖ / ‖u‖ := rfl
  have hD : detuneD δ y = ‖u + (q : ℂ) * v‖ / ‖u‖ := rfl
  have hRpos : 0 < detuneR δ y := by rw [hR]; positivity
  -- the norm square of the sum
  have hN2 : ‖u + (q : ℂ) * v‖ ^ 2 = ‖u‖ ^ 2 + 2 * q * (u.re * v.re + u.im * v.im) + q ^ 2 * ‖v‖ ^ 2 := by
    rw [norm_sq_eq_re_im, norm_sq_eq_re_im, norm_sq_eq_re_im]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, add_zero]
    ring
  -- the cross term
  have hδy : |u.im| ≤ 1 / 4 := a3.trans (by nlinarith only [hδ1, hy1, hy0, hδ0])
  have hcross : 1 / 2 * (v.re * u.re) ≤ u.re * v.re + u.im * v.im := by
    have h1 : |u.im * v.im| ≤ v.re * (1 / 4) := by
      rw [abs_mul]
      calc |u.im| * |v.im| ≤ (1 / 4) * v.re := mul_le_mul hδy b2 (abs_nonneg _) (by norm_num)
        _ = v.re * (1 / 4) := by ring
    have h2 := (abs_le.mp h1).1
    nlinarith only [h2, a1, b1]
  have hcross0 : 0 ≤ u.re * v.re + u.im * v.im := by nlinarith only [hcross, a1, b1, mul_pos (by linarith : (0 : ℝ) < u.re) b1]
  have hNpos : 0 < ‖u + (q : ℂ) * v‖ := by
    have : 0 < ‖u + (q : ℂ) * v‖ ^ 2 := by
      rw [hN2]
      have : 0 < q ^ 2 * ‖v‖ ^ 2 := by positivity
      nlinarith only [this, hcross0, hq0, sq_nonneg ‖u‖, hu0]
    exact lt_of_le_of_ne (norm_nonneg _) (fun h => by rw [← h] at this; simp at this)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hD, lt_div_iff₀ hu0, one_mul]
    have : ‖u‖ ^ 2 < ‖u + (q : ℂ) * v‖ ^ 2 := by
      rw [hN2]
      have : 0 < q ^ 2 * ‖v‖ ^ 2 := by positivity
      nlinarith only [this, hcross0, hq0]
    exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) this
  · rw [hD, hR, div_le_iff₀ hu0]
    have : ‖u + (q : ℂ) * v‖ ≤ ‖u‖ + q * ‖v‖ := by
      calc ‖u + (q : ℂ) * v‖ ≤ ‖u‖ + ‖(q : ℂ) * v‖ := norm_add_le _ _
        _ = ‖u‖ + q * ‖v‖ := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq0]
    have e : (1 + q * ‖v‖ / ‖u‖) * ‖u‖ = ‖u‖ + q * ‖v‖ := by field_simp
    linarith
  · -- lower bound
    have hvre : 7 / 10 * ‖v‖ ≤ v.re := by
      apply le_of_sq_le' b1.le
      rw [mul_pow, norm_sq_eq_re_im]
      have : v.im ^ 2 ≤ v.re ^ 2 := by
        have := sq_abs v.im
        nlinarith only [b2, abs_nonneg v.im, this, b1]
      nlinarith only [this, sq_nonneg v.re]
    have hure : 4 / 5 * ‖u‖ ≤ u.re := by
      apply le_of_sq_le' (by linarith)
      rw [mul_pow, norm_sq_eq_re_im]
      have : u.im ^ 2 ≤ (u.re / 2) ^ 2 := by
        have h1 : |u.im| ≤ u.re / 2 := hδy.trans (by linarith)
        have := sq_abs u.im
        nlinarith only [h1, abs_nonneg u.im, this]
      nlinarith only [this, sq_nonneg u.re]
    have hD1 : 1 < detuneD δ y := by
      rw [hD, lt_div_iff₀ hu0, one_mul]
      have : ‖u‖ ^ 2 < ‖u + (q : ℂ) * v‖ ^ 2 := by
        rw [hN2]
        have : 0 < q ^ 2 * ‖v‖ ^ 2 := by positivity
        nlinarith only [this, hcross0, hq0]
      exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) this
    have hD2 : detuneD δ y ^ 2 = 1 + 2 * q * (u.re * v.re + u.im * v.im) / ‖u‖ ^ 2 + detuneR δ y ^ 2 := by
      rw [hD, hR, div_pow, hN2]; field_simp
    have hcr : 14 / 25 * detuneR δ y ≤ 2 * q * (u.re * v.re + u.im * v.im) / ‖u‖ ^ 2 := by
      rw [hR, le_div_iff₀ (by positivity)]
      have h1 : 14 / 25 * (q * ‖v‖ / ‖u‖) * ‖u‖ ^ 2 = 14 / 25 * q * ‖v‖ * ‖u‖ := by field_simp
      rw [h1]
      have h2 : (7 / 10 * ‖v‖) * (4 / 5 * ‖u‖) ≤ v.re * u.re :=
        mul_le_mul hvre hure (by positivity) b1.le
      nlinarith only [h2, hcross, hq0, mul_le_mul_of_nonneg_left h2 hq0.le]
    have hDle : detuneD δ y ≤ 1 + detuneR δ y := by
      rw [hD, hR, div_le_iff₀ hu0]
      have : ‖u + (q : ℂ) * v‖ ≤ ‖u‖ + q * ‖v‖ := by
        calc ‖u + (q : ℂ) * v‖ ≤ ‖u‖ + ‖(q : ℂ) * v‖ := norm_add_le _ _
          _ = ‖u‖ + q * ‖v‖ := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq0]
      have e : (1 + q * ‖v‖ / ‖u‖) * ‖u‖ = ‖u‖ + q * ‖v‖ := by field_simp
      linarith
    have hsq2 : √2 ≤ 142 / 100 := by
      have hu : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      nlinarith only [hu, Real.sqrt_nonneg 2]
    have hD3 : detuneD δ y + 1 ≤ 7 / 2 := by linarith only [hDle, hRle, hsq2]
    have : (detuneD δ y - 1) * (detuneD δ y + 1) = detuneD δ y ^ 2 - 1 := by ring
    nlinarith only [this, hD2, hcr, hD3, hD1, sq_nonneg (detuneR δ y), hRpos,
      mul_le_mul_of_nonneg_left hD3 (by linarith : (0 : ℝ) ≤ detuneD δ y - 1)]
  · have hDle : detuneD δ y ≤ 1 + detuneR δ y := by
      rw [hD, hR, div_le_iff₀ hu0]
      have : ‖u + (q : ℂ) * v‖ ≤ ‖u‖ + q * ‖v‖ := by
        calc ‖u + (q : ℂ) * v‖ ≤ ‖u‖ + ‖(q : ℂ) * v‖ := norm_add_le _ _
          _ = ‖u‖ + q * ‖v‖ := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq0]
      have e : (1 + q * ‖v‖ / ‖u‖) * ‖u‖ = ‖u‖ + q * ‖v‖ := by field_simp
      linarith
    linarith

/-- `R_δ⁴ ≍ y^{10}/(δ+y)²`, i.e. `R_δ ≍ y^{5/2}(δ+y)^{-1/2}` (`cts:smooth-env` (3)), with absolute constants,
for `0 < δ ≤ 1/4`, `y ∈ (0,1)`. -/
theorem detuneR_pow4_bounds {y δ : ℝ} (hy0 : 0 < y) (hy1 : y < 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 4) :
    9 / 16 * (y ^ 10 / (δ + y) ^ 2) ≤ detuneR δ y ^ 4 ∧
      detuneR δ y ^ 4 ≤ 2048 * (y ^ 10 / (δ + y) ^ 2) := by
  have hδ1' : δ < 1 := by linarith
  have hR4 : detuneR δ y ^ 4 = qSlit y ^ 4 * (4 * y ^ 2 / (δ ^ 2 + (2 - δ) ^ 2 * y ^ 2)) *
      ((1 + (1 - δ) ^ 2 * y ^ 2) / (1 + y ^ 2)) := by
    unfold detuneR
    rw [div_pow, mul_pow, norm_mEps_arc_pow4 hy0 hδ0 hδ1', norm_mEps_slit_pow4 hy0 hy1 hδ0 hδ1']
    have hA : 0 < 1 + (1 - δ) ^ 2 * y ^ 2 := by positivity
    have hB : 0 < 1 + y ^ 2 := by positivity
    field_simp
  obtain ⟨hq1, -, hq2⟩ := qSlit_bounds hy0 hy1
  have hden : 0 < δ ^ 2 + (2 - δ) ^ 2 * y ^ 2 := by positivity
  have hdy : 0 < (δ + y) ^ 2 := by positivity
  -- denominator bounds
  have hA1 : 0 ≤ (2 - δ) ^ 2 - 1 := by nlinarith only [hδ1, hδ0]
  have hA2 : 0 ≤ 4 - (2 - δ) ^ 2 := by nlinarith only [hδ1, hδ0]
  have hd1 : (δ + y) ^ 2 / 2 ≤ δ ^ 2 + (2 - δ) ^ 2 * y ^ 2 := by
    nlinarith only [sq_nonneg (δ - y), sq_nonneg y, mul_nonneg hA1 (sq_nonneg y)]
  have hd2 : δ ^ 2 + (2 - δ) ^ 2 * y ^ 2 ≤ 4 * (δ + y) ^ 2 := by
    nlinarith only [sq_nonneg y, sq_nonneg δ, mul_nonneg hδ0.le hy0.le, hδ0, hδ1,
      mul_nonneg hA2 (sq_nonneg y)]
  have hr1 : y ^ 2 / (δ + y) ^ 2 ≤ 4 * y ^ 2 / (δ ^ 2 + (2 - δ) ^ 2 * y ^ 2) := by
    rw [div_le_div_iff₀ hdy hden]
    nlinarith only [hd2, sq_nonneg y]
  have hr2 : 4 * y ^ 2 / (δ ^ 2 + (2 - δ) ^ 2 * y ^ 2) ≤ 8 * y ^ 2 / (δ + y) ^ 2 := by
    rw [div_le_div_iff₀ hden hdy]
    nlinarith only [hd1, sq_nonneg y]
  have hs1 : 9 / 16 ≤ (1 + (1 - δ) ^ 2 * y ^ 2) / (1 + y ^ 2) := by
    rw [le_div_iff₀ (by positivity)]
    have : 9 / 16 ≤ (1 - δ) ^ 2 := by nlinarith only [hδ1, hδ0]
    nlinarith only [this, sq_nonneg y]
  have hs2 : (1 + (1 - δ) ^ 2 * y ^ 2) / (1 + y ^ 2) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have : (1 - δ) ^ 2 ≤ 1 := by nlinarith only [hδ1, hδ0]
    nlinarith only [this, sq_nonneg y]
  have hq4a : (y ^ 2) ^ 4 ≤ qSlit y ^ 4 := pow_le_pow_left₀ (by positivity) hq1 4
  have hq4b : qSlit y ^ 4 ≤ (4 * y ^ 2) ^ 4 :=
    pow_le_pow_left₀ ((by positivity : 0 ≤ y ^ 2).trans hq1) hq2 4
  have hq0 : 0 ≤ qSlit y ^ 4 := by positivity
  have e10 : y ^ 10 = y ^ 8 * y ^ 2 := by ring
  rw [hR4]
  constructor
  · have h1 : (y ^ 2) ^ 4 * (y ^ 2 / (δ + y) ^ 2) * (9 / 16) ≤
        qSlit y ^ 4 * (4 * y ^ 2 / (δ ^ 2 + (2 - δ) ^ 2 * y ^ 2)) *
          ((1 + (1 - δ) ^ 2 * y ^ 2) / (1 + y ^ 2)) := by
      gcongr
    calc 9 / 16 * (y ^ 10 / (δ + y) ^ 2) = (y ^ 2) ^ 4 * (y ^ 2 / (δ + y) ^ 2) * (9 / 16) := by
          rw [e10]; ring
      _ ≤ _ := h1
  · have h1 : qSlit y ^ 4 * (4 * y ^ 2 / (δ ^ 2 + (2 - δ) ^ 2 * y ^ 2)) *
        ((1 + (1 - δ) ^ 2 * y ^ 2) / (1 + y ^ 2)) ≤
        (4 * y ^ 2) ^ 4 * (8 * y ^ 2 / (δ + y) ^ 2) * 1 := by
      gcongr
    calc _ ≤ _ := h1
      _ = 2048 * (y ^ 10 / (δ + y) ^ 2) := by rw [e10]; ring

/-- `1 + √2 < cosh(π/2)`. -/
lemma one_add_sqrt_two_lt_cosh : 1 + √2 < Real.cosh (π / 2) := by
  have hp := Real.pi_gt_d2
  have hp2 := Real.pi_lt_d2
  have hu : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hu0 := Real.sqrt_nonneg 2
  have hsq : √2 ≤ 142 / 100 := by nlinarith only [hu, hu0]
  have t0 : 0 ≤ π / 4 := by positivity
  have t1 : π / 4 ≤ 1 := by linarith
  have hc : 1 + (π / 4) ^ 2 / 2 + (π / 4) ^ 4 / 24 ≤ Real.cosh (π / 4) := (cosh_bounds t0 t1).1
  have h2 : Real.cosh (π / 2) = 2 * Real.cosh (π / 4) ^ 2 - 1 := by
    rw [show π / 2 = 2 * (π / 4) by ring, Real.cosh_two_mul, Real.cosh_sq]; ring_nf
  have hπ4 : 785 / 1000 ≤ π / 4 := by linarith
  have hs2 : (785 / 1000) ^ 2 ≤ (π / 4) ^ 2 := pow_le_pow_left₀ (by norm_num) hπ4 2
  have hs4 : (785 / 1000) ^ 4 ≤ (π / 4) ^ 4 := pow_le_pow_left₀ (by norm_num) hπ4 4
  have hc1 : 132 / 100 ≤ Real.cosh (π / 4) := by
    norm_num at hs2 hs4
    linarith only [hc, hs2, hs4]
  rw [h2]
  nlinarith only [hc1, hsq]

/-- For `F_* = (1+z²)/G`: `K(y) F_*(e^{-iψ}) = q(y) F_*(iy)` (the phase-locking `cts:eta-opt`, complex form). -/
lemma fStar_edge_eq {W : ℝ → ℝ} {K : ℝ → ℂ} {G : ℂ → ℂ} {g1 : ℝ} (hG : OuterDatum W K g1 G)
    {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    K y * fStar G (starRingEnd ℂ (wPt y)) = (qSlit y : ℂ) * fStar G (Complex.I * (y : ℂ)) := by
  obtain ⟨hy0, hy1⟩ := hy
  have hfG : ∀ z ∈ closure halfDisc \ singPts, fStar G z * G z = 1 + z ^ 2 := by
    intro z hz
    unfold fStar
    exact div_mul_cancel₀ _ (hG.ne_zero z hz)
  have e1 := hfG _ (I_mul_mem_cont hy0 hy1)
  have e2 := hfG _ (wbar_mem_cont hy0 hy1)
  have hc := hG.coupling y ⟨hy0, hy1⟩
  have hGne : G (Complex.I * (y : ℂ)) ≠ 0 := hG.ne_zero _ (I_mul_mem_cont hy0 hy1)
  have hedge : G (Complex.I * (y : ℂ)) * (fStar G (Complex.I * (y : ℂ)) +
      K y * fStar G (starRingEnd ℂ (wPt y))) = edgeSum (fun z => 1 + z ^ 2) y := by
    unfold edgeSum
    beta_reduce
    rw [← e1, ← e2]
    calc _ = fStar G (Complex.I * (y : ℂ)) * G (Complex.I * (y : ℂ)) +
          (G (Complex.I * (y : ℂ)) * K y) * fStar G (starRingEnd ℂ (wPt y)) := by ring
      _ = _ := by rw [hc]; ring
  have hA : G (Complex.I * (y : ℂ)) * fStar G (Complex.I * (y : ℂ)) = ((1 - y ^ 2 : ℝ) : ℂ) := by
    rw [mul_comm, e1]; push_cast; rw [mul_pow, Complex.I_sq]; ring
  rw [edgeSum_one_add_sq] at hedge
  apply mul_left_cancel₀ hGne
  have hy2 : (1 + y ^ 2 : ℝ) ≠ 0 := by positivity
  have hy2' : (1 + (y : ℂ) ^ 2) ≠ 0 := by exact_mod_cast hy2
  have : G (Complex.I * (y : ℂ)) * (K y * fStar G (starRingEnd ℂ (wPt y))) =
      G (Complex.I * (y : ℂ)) * (fStar G (Complex.I * (y : ℂ)) +
        K y * fStar G (starRingEnd ℂ (wPt y))) -
      G (Complex.I * (y : ℂ)) * fStar G (Complex.I * (y : ℂ)) := by ring
  rw [this, hedge, hA,
    show G (Complex.I * (y : ℂ)) * ((qSlit y : ℂ) * fStar G (Complex.I * (y : ℂ))) =
      (qSlit y : ℂ) * (G (Complex.I * (y : ℂ)) * fStar G (Complex.I * (y : ℂ))) by ring, hA,
    ← Complex.ofReal_mul, ← Complex.ofReal_sub]
  congr 1
  unfold qSlit
  field_simp
  ring

/-- **The detuning of the smoothed minimiser** (`cts:Rdelta`): for `F_δ = m_δ F_*` on the slit and the arc,
`|F_δ(iy) + K(y) F_δ(e^{-iψ})| = D_δ(y) |F_δ(iy)|` and `|K(y) F_δ(e^{-iψ})| = R_δ(y) |F_δ(iy)|`. -/
theorem fDelta_edge_ratio {W : ℝ → ℝ} {K : ℝ → ℂ} {G : ℂ → ℂ} {g1 δ : ℝ} (hG : OuterDatum W K g1 G)
    {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ‖fDelta G δ (Complex.I * (y : ℂ)) + K y * fDelta G δ (starRingEnd ℂ (wPt y))‖ =
        detuneD δ y * ‖fDelta G δ (Complex.I * (y : ℂ))‖ ∧
      ‖K y * fDelta G δ (starRingEnd ℂ (wPt y))‖ = detuneR δ y * ‖fDelta G δ (Complex.I * (y : ℂ))‖ := by
  obtain ⟨hy0, hy1⟩ := hy
  have hu1 := one_le_norm_mEps_slit hy0 hy1 hδ0 hδ1
  have hu0 : 0 < ‖mEps δ (Complex.I * (y : ℂ))‖ := by linarith
  have hq0 : 0 ≤ qSlit y := (by positivity : 0 ≤ y ^ 2).trans (qSlit_bounds hy0 hy1).1
  have he := fStar_edge_eq hG ⟨hy0, hy1⟩
  have h1 : fDelta G δ (Complex.I * (y : ℂ)) + K y * fDelta G δ (starRingEnd ℂ (wPt y)) =
      fStar G (Complex.I * (y : ℂ)) * (mEps δ (Complex.I * (y : ℂ)) +
        (qSlit y : ℂ) * mEps δ (starRingEnd ℂ (wPt y))) := by
    unfold fDelta
    calc _ = mEps δ (Complex.I * (y : ℂ)) * fStar G (Complex.I * (y : ℂ)) +
          mEps δ (starRingEnd ℂ (wPt y)) * (K y * fStar G (starRingEnd ℂ (wPt y))) := by ring
      _ = _ := by rw [he]; ring
  have h2 : K y * fDelta G δ (starRingEnd ℂ (wPt y)) =
      fStar G (Complex.I * (y : ℂ)) * ((qSlit y : ℂ) * mEps δ (starRingEnd ℂ (wPt y))) := by
    unfold fDelta
    calc _ = mEps δ (starRingEnd ℂ (wPt y)) * (K y * fStar G (starRingEnd ℂ (wPt y))) := by ring
      _ = _ := by rw [he]; ring
  have h3 : ‖fDelta G δ (Complex.I * (y : ℂ))‖ =
      ‖mEps δ (Complex.I * (y : ℂ))‖ * ‖fStar G (Complex.I * (y : ℂ))‖ := by
    unfold fDelta; rw [norm_mul]
  constructor
  · rw [h1, norm_mul, h3]
    unfold detuneD
    field_simp
  · rw [h2, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq0, h3]
    unfold detuneR
    field_simp

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.detuneD_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms detuneD_bounds

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.detuneR_pow4_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms detuneR_pow4_bounds

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.one_add_sqrt_two_lt_cosh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms one_add_sqrt_two_lt_cosh

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.fStar_edge_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fStar_edge_eq

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.fDelta_edge_ratio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fDelta_edge_ratio

end FormalResearch.ModularBootstrap.FiveTerm
