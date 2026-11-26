module

public import FormalResearch.ModularBootstrap.FiveTerm.Regulariser

/-!
# The defect of `H_ε = m_ε (1+z²)` is `O(ε² y²)` (FIVE-0; `ctu:common-functional` (3))

Source: `CFT/modular_bootstrap/paper/constant_term_universality.tex`, Lemma ctu.2a (3), the display after
"Finally `Re m_ε(iy) ≥ cos(π/8) > 1/2` ...".

Write `u = m_ε(iy)`, `v = m_ε(e^{-iψ})`, `q = 4y²/(1+y²)²`.  Then `B_{H_ε} = (1-y²)(u + q v)`,
`u² = (1-iy)/(1-(1-ε)iy)` and `v² = 2iy/(ε + i(2-ε)y)` have positive real part, so `|Im u| ≤ Re u`,
`|Im v| ≤ Re v`, whence `|B_H| ≥ |H(iy)|` and `Re B_H ≥ (1-y²)/2`.  The sharp estimates `|Im u| ≤ ε y`,
`q Im v ≤ 4 ε y` give `defectNum H_ε y ≤ 25 ε² y²` (`defectInt_reg_le`: `defectInt H_ε y ≤ 25 ε²`).
All proved unconditionally; the constant is absolute.
-/

@[expose] public section

open Complex Set Filter Topology MeasureTheory Metric
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm

/-- Real facts about a square root `u1 + i u2` of `P + iQ` with `P > 0`, `u1 > 0`, `P² + Q² ≥ 1`. -/
lemma sqrt_fact_u {u1 u2 P Q : ℝ} (hu1 : 0 < u1) (h1 : u1 ^ 2 - u2 ^ 2 = P) (h2 : 2 * u1 * u2 = Q)
    (hP : 0 < P) (hPQ : 1 ≤ P ^ 2 + Q ^ 2) :
    1 / 2 ≤ u1 ∧ |u2| ≤ u1 ∧ |u2| ≤ |Q| := by
  have hsq : u2 ^ 2 ≤ u1 ^ 2 := by nlinarith only [h1, hP]
  have habs : |u2| ≤ u1 := by
    apply abs_le.mpr
    constructor <;> nlinarith only [hsq, hu1]
  have hS : 1 ≤ u1 ^ 2 + u2 ^ 2 := by
    have e : (u1 ^ 2 + u2 ^ 2) ^ 2 = P ^ 2 + Q ^ 2 := by rw [← h1, ← h2]; ring
    by_contra hcon
    push Not at hcon
    have h0 : 0 ≤ u1 ^ 2 + u2 ^ 2 := by positivity
    nlinarith only [e, hcon, hPQ, h0]
  have hu1h : 1 / 2 ≤ u1 := by nlinarith only [hS, hsq, hu1]
  refine ⟨hu1h, habs, ?_⟩
  have : |Q| = 2 * u1 * |u2| := by
    rw [← h2, abs_mul, abs_mul, abs_of_pos hu1]; norm_num
  rw [this]
  nlinarith only [hu1h, abs_nonneg u2]

/-- Real facts about a square root `v1 + i v2` of `P + iQ` with `P, Q > 0`, `v1 > 0`:
`v2 ≤ v1` and `v2⁴ (P² + Q²) ≤ Q⁴ / 4`. -/
lemma sqrt_fact_v {v1 v2 P Q : ℝ} (hv1 : 0 < v1) (h1 : v1 ^ 2 - v2 ^ 2 = P) (h2 : 2 * v1 * v2 = Q)
    (hP : 0 < P) (hQ : 0 < Q) :
    0 < v2 ∧ v2 ≤ v1 ∧ v2 ^ 4 * (P ^ 2 + Q ^ 2) ≤ Q ^ 4 / 4 := by
  have hv2 : 0 < v2 := by
    by_contra hcon
    push Not at hcon
    nlinarith only [h2, hQ, hv1, hcon]
  have hsq : v2 ^ 2 ≤ v1 ^ 2 := by nlinarith only [h1, hP]
  have hle : v2 ≤ v1 := by nlinarith only [hsq, hv1, hv2]
  refine ⟨hv2, hle, ?_⟩
  have e : (v1 ^ 2 + v2 ^ 2) ^ 2 = P ^ 2 + Q ^ 2 := by rw [← h1, ← h2]; ring
  have h4 : P ^ 2 + Q ^ 2 ≤ 4 * v1 ^ 4 := by
    rw [← e]
    nlinarith only [hsq, sq_nonneg v1, sq_nonneg v2]
  have hQ4 : Q ^ 4 = 16 * (v1 * v2) ^ 4 := by rw [← h2]; ring
  calc v2 ^ 4 * (P ^ 2 + Q ^ 2) ≤ v2 ^ 4 * (4 * v1 ^ 4) := by gcongr
    _ = 4 * (v1 * v2) ^ 4 := by ring
    _ = Q ^ 4 / 4 := by rw [hQ4]; ring

section

variable {ε y : ℝ}

/-- The slit square root: `v2 ≤ ε / y` for the square root of `v² = 2iy/(ε + i(2-ε)y)`. -/
lemma v2_le_aux {v1 v2 : ℝ} (hy0 : 0 < y) (hε0 : 0 < ε) (hε1 : ε < 1) (hv1 : 0 < v1)
    (h1 : v1 ^ 2 - v2 ^ 2 = 2 * (2 - ε) * y ^ 2 / (ε ^ 2 + (2 - ε) ^ 2 * y ^ 2))
    (h2 : 2 * v1 * v2 = 2 * y * ε / (ε ^ 2 + (2 - ε) ^ 2 * y ^ 2)) :
    0 < v2 ∧ v2 ≤ v1 ∧ v2 ≤ ε / y := by
  have hD : 0 < ε ^ 2 + (2 - ε) ^ 2 * y ^ 2 := by positivity
  have hP : 0 < 2 * (2 - ε) * y ^ 2 / (ε ^ 2 + (2 - ε) ^ 2 * y ^ 2) := by
    apply div_pos _ hD
    have : 0 < 2 - ε := by linarith
    positivity
  have hQ : 0 < 2 * y * ε / (ε ^ 2 + (2 - ε) ^ 2 * y ^ 2) := by positivity
  obtain ⟨hv2, hle, h4⟩ := sqrt_fact_v hv1 h1 h2 hP hQ
  refine ⟨hv2, hle, ?_⟩
  set D := ε ^ 2 + (2 - ε) ^ 2 * y ^ 2 with hDdef
  have hS : (2 * (2 - ε) * y ^ 2 / D) ^ 2 + (2 * y * ε / D) ^ 2 = 4 * y ^ 2 / D := by
    rw [hDdef]; field_simp; ring
  have hyD : y ^ 2 ≤ D := by
    have h21 : 1 ≤ (2 - ε) ^ 2 := by nlinarith only [hε1]
    rw [hDdef]
    nlinarith only [sq_nonneg ε, mul_le_mul_of_nonneg_right h21 (sq_nonneg y)]
  have hy6 : y ^ 6 ≤ D ^ 3 := by
    calc y ^ 6 = (y ^ 2) ^ 3 := by ring
      _ ≤ D ^ 3 := by gcongr
  rw [hS] at h4
  have hQ4 : (2 * y * ε / D) ^ 4 / 4 = 4 * y ^ 4 * ε ^ 4 / D ^ 4 := by field_simp; ring
  rw [hQ4] at h4
  by_contra hcon
  push Not at hcon
  have ht0 : 0 < ε / y := by positivity
  have hpow : (ε / y) ^ 4 < v2 ^ 4 := by gcongr
  have hDpos : 0 < D := hD
  have hlow : 4 * y ^ 4 * ε ^ 4 / D ^ 4 < v2 ^ 4 * (4 * y ^ 2 / D) := by
    have h5 : 4 * y ^ 4 * ε ^ 4 / D ^ 4 ≤ (ε / y) ^ 4 * (4 * y ^ 2 / D) := by
      rw [div_pow, div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
      have : 0 ≤ 4 * y ^ 2 * ε ^ 4 := by positivity
      nlinarith only [hy6, this, hDpos, mul_nonneg this (sub_nonneg.mpr hy6)]
    calc _ ≤ (ε / y) ^ 4 * (4 * y ^ 2 / D) := h5
      _ < v2 ^ 4 * (4 * y ^ 2 / D) := by gcongr
  linarith only [h4, hlow]


lemma norm_I_mul_le (hy0 : 0 < y) (hy1 : y < 1) : ‖Complex.I * (y : ℂ)‖ ≤ 1 := by
  simpa using norm_closure_halfDisc_le (I_mul_mem_cont hy0 hy1).1

lemma I_mul_ne_one : Complex.I * (y : ℂ) ≠ 1 := by
  intro h; have := congrArg Complex.re h; simp at this

lemma norm_wbar_le : ‖starRingEnd ℂ (wPt y)‖ ≤ 1 := by
  rw [Complex.norm_conj, norm_wPt]

lemma wbar_ne_one (hy0 : 0 < y) : starRingEnd ℂ (wPt y) ≠ 1 := by
  intro h
  have := congrArg Complex.im h
  rw [Complex.conj_im, im_wPt] at this
  simp only [Complex.one_im] at this
  have : 0 < 2 * y / (1 + y ^ 2) := by positivity
  linarith

lemma mEps_slit_sq (hy0 : 0 < y) (hy1 : y < 1) (hε0 : 0 < ε) (hε1 : ε < 1) :
    mEps ε (Complex.I * (y : ℂ)) ^ 2 =
      (((1 + (1 - ε) * y ^ 2) / (1 + (1 - ε) ^ 2 * y ^ 2) : ℝ) : ℂ) +
        ((-(ε * y) / (1 + (1 - ε) ^ 2 * y ^ 2) : ℝ) : ℂ) * Complex.I := by
  have hz := norm_I_mul_le hy0 hy1
  rw [mEps_sq hz I_mul_ne_one hε0 hε1]
  have hne : 1 - ((1 - ε : ℝ) : ℂ) * (Complex.I * (y : ℂ)) ≠ 0 :=
    Complex.slitPlane_ne_zero (one_sub_mul_mem_slitPlane hz hε0 hε1)
  rw [div_eq_iff hne]
  have hA : (1 + (1 - ε) ^ 2 * y ^ 2) ≠ 0 := by positivity
  apply Complex.ext
  · simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im]
    field_simp
    ring
  · simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im]
    field_simp
    ring

lemma mEps_arc_sq (hy0 : 0 < y) (hε0 : 0 < ε) (hε1 : ε < 1) :
    mEps ε (starRingEnd ℂ (wPt y)) ^ 2 =
      ((2 * (2 - ε) * y ^ 2 / (ε ^ 2 + (2 - ε) ^ 2 * y ^ 2) : ℝ) : ℂ) +
        ((2 * y * ε / (ε ^ 2 + (2 - ε) ^ 2 * y ^ 2) : ℝ) : ℂ) * Complex.I := by
  have hz := norm_wbar_le (y := y)
  rw [mEps_sq hz (wbar_ne_one hy0) hε0 hε1]
  have hne : 1 - ((1 - ε : ℝ) : ℂ) * starRingEnd ℂ (wPt y) ≠ 0 :=
    Complex.slitPlane_ne_zero (one_sub_mul_mem_slitPlane hz hε0 hε1)
  rw [div_eq_iff hne]
  have hD : (ε ^ 2 + (2 - ε) ^ 2 * y ^ 2) ≠ 0 := by positivity
  have hy2 : (1 + y ^ 2) ≠ 0 := by positivity
  apply Complex.ext
  · simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im,
      Complex.conj_re, Complex.conj_im, re_wPt, im_wPt]
    field_simp
    ring
  · simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im,
      Complex.conj_re, Complex.conj_im, re_wPt, im_wPt]
    field_simp
    ring


/-- The core defect estimate: for `T = u + q v` with `Re u ≥ 1/2`, `|Im u| ≤ Re u`, `|Im v| ≤ Re v`,
`max(ρ|u|, ρ|T|) - ρ Re T ≤ ρ (Im T)²`. -/
lemma defect_core {u v : ℂ} {q ρ : ℝ} (hq : 0 ≤ q) (hρ : 0 < ρ) (hu1 : 1 / 2 ≤ u.re)
    (hu2 : |u.im| ≤ u.re) (hv1 : 0 ≤ v.re) (hv2 : |v.im| ≤ v.re) :
    max (ρ * ‖u‖) (ρ * ‖u + (q : ℂ) * v‖) - ρ * (u + (q : ℂ) * v).re ≤ ρ * (u + (q : ℂ) * v).im ^ 2 := by
  set T : ℂ := u + (q : ℂ) * v with hT
  have hT1 : T.re = u.re + q * v.re := by simp [hT]
  have hT2 : T.im = u.im + q * v.im := by simp [hT]
  have hnT : ‖T‖ ^ 2 = T.re ^ 2 + T.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hnu : ‖u‖ ^ 2 = u.re ^ 2 + u.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hcross : 0 ≤ u.re * v.re + u.im * v.im := by
    have h1 : |u.im * v.im| ≤ u.re * v.re := by
      rw [abs_mul]; exact mul_le_mul hu2 hv2 (abs_nonneg _) (by linarith)
    have := neg_abs_le (u.im * v.im)
    linarith
  have hle : ‖u‖ ≤ ‖T‖ := by
    apply le_of_sq_le_sq _ (norm_nonneg _)
    rw [hnT, hnu, hT1, hT2]
    nlinarith only [hcross, hq, mul_nonneg hq hcross, sq_nonneg (q * v.re), sq_nonneg (q * v.im)]
  rw [max_eq_right (mul_le_mul_of_nonneg_left hle hρ.le)]
  have hRe : 1 / 2 ≤ T.re := by rw [hT1]; nlinarith only [hu1, hq, hv1, mul_nonneg hq hv1]
  have hN0 : 0 ≤ ‖T‖ := norm_nonneg _
  have hNT : T.re ≤ ‖T‖ := Complex.re_le_norm T
  have hkey : ‖T‖ - T.re ≤ T.im ^ 2 := by
    nlinarith only [hnT, hRe, hNT, hN0, mul_nonneg (sub_nonneg.mpr hNT) (show 0 ≤ ‖T‖ + T.re - 1 by linarith)]
  nlinarith only [hkey, hρ]


lemma edgeSum_reg (ε y : ℝ) :
    edgeSum (fun z => mEps ε z * (1 + z ^ 2)) y =
      ((1 - y ^ 2 : ℝ) : ℂ) * (mEps ε (Complex.I * (y : ℂ)) +
        ((4 * y ^ 2 / (1 + y ^ 2) ^ 2 : ℝ) : ℂ) * mEps ε (starRingEnd ℂ (wPt y))) := by
  unfold edgeSum
  beta_reduce
  have h1 := wPt_mul_conj y
  have h2 := Complex.add_conj (wPt y)
  rw [re_wPt] at h2
  have hI : (1 : ℂ) + (Complex.I * (y : ℂ)) ^ 2 = ((1 - y ^ 2 : ℝ) : ℂ) := by
    push_cast; rw [mul_pow, Complex.I_sq]; ring
  rw [hI]
  push_cast at h2 ⊢
  have hne : (1 + (y : ℂ) ^ 2) ≠ 0 := by
    have : (1 + y ^ 2 : ℝ) ≠ 0 := by positivity
    exact_mod_cast this
  linear_combination (norm := (field_simp; ring))
    (2 * (y : ℂ) ^ 2 / (1 + (y : ℂ) ^ 2) * mEps ε (starRingEnd ℂ (wPt y)) *
      starRingEnd ℂ (wPt y)) * h1 +
    (2 * (y : ℂ) ^ 2 / (1 + (y : ℂ) ^ 2) * mEps ε (starRingEnd ℂ (wPt y))) * h2

/-- Real and imaginary parts of the slit value `u = m_ε(iy)`. -/
lemma slit_facts (hy0 : 0 < y) (hy1 : y < 1) (hε0 : 0 < ε) (hε1 : ε < 1) :
    1 / 2 ≤ (mEps ε (Complex.I * (y : ℂ))).re ∧
    |(mEps ε (Complex.I * (y : ℂ))).im| ≤ (mEps ε (Complex.I * (y : ℂ))).re ∧
    |(mEps ε (Complex.I * (y : ℂ))).im| ≤ ε * y := by
  have hsq := mEps_slit_sq hy0 hy1 hε0 hε1
  have hpos := re_mEps_pos (norm_I_mul_le hy0 hy1) I_mul_ne_one hε0 hε1
  set u := mEps ε (Complex.I * (y : ℂ)) with hu
  have hre := congrArg Complex.re hsq
  have him := congrArg Complex.im hsq
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero,
    zero_add] at hre him
  have hA : 0 < 1 + (1 - ε) ^ 2 * y ^ 2 := by positivity
  have hP : 0 < (1 + (1 - ε) * y ^ 2) / (1 + (1 - ε) ^ 2 * y ^ 2) := by
    apply div_pos _ hA
    have : 0 < 1 - ε := by linarith
    positivity
  have hPQ : 1 ≤ ((1 + (1 - ε) * y ^ 2) / (1 + (1 - ε) ^ 2 * y ^ 2)) ^ 2 +
      (-(ε * y) / (1 + (1 - ε) ^ 2 * y ^ 2)) ^ 2 := by
    rw [div_pow, div_pow, ← add_div, le_div_iff₀ (by positivity)]
    have h1 : 0 < 1 - ε := by linarith
    nlinarith only [mul_pos h1 hε0, mul_nonneg (mul_nonneg h1.le h1.le) (sq_nonneg y),
      sq_nonneg (ε * y), mul_pos hy0 hy0, mul_nonneg (sq_nonneg (1 - ε)) (sq_nonneg (y ^ 2)),
      mul_nonneg (mul_pos h1 hε0).le (sq_nonneg y), mul_nonneg (sq_nonneg y) (sq_nonneg ε),
      mul_nonneg (mul_nonneg h1.le hε0.le) (sq_nonneg (y ^ 2)), mul_nonneg (sq_nonneg ((1 - ε) * y))
        (mul_nonneg h1.le (add_pos h1 hε0).le), sq_nonneg y]
  obtain ⟨a1, a2, a3⟩ := sqrt_fact_u (u1 := u.re) (u2 := u.im) hpos (by
      calc u.re ^ 2 - u.im ^ 2 = u.re * u.re - u.im * u.im := by ring
        _ = _ := hre
        _ = _ := by ring) (by
      calc 2 * u.re * u.im = u.re * u.im + u.im * u.re := by ring
        _ = _ := him
        _ = _ := by ring) hP hPQ
  refine ⟨a1, a2, le_trans a3 ?_⟩
  rw [abs_div, abs_neg, abs_of_pos hA, abs_of_pos (mul_pos hε0 hy0)]
  rw [div_le_iff₀ hA]
  nlinarith only [mul_pos hε0 hy0, sq_nonneg (1 - ε), sq_nonneg y, mul_nonneg (mul_pos hε0 hy0).le (mul_nonneg (sq_nonneg (1 - ε)) (sq_nonneg y))]


/-- The arc value `v = m_ε(e^{-iψ})`. -/
lemma arc_facts (hy0 : 0 < y) (hε0 : 0 < ε) (hε1 : ε < 1) :
    0 < (mEps ε (starRingEnd ℂ (wPt y))).re ∧
    |(mEps ε (starRingEnd ℂ (wPt y))).im| ≤ (mEps ε (starRingEnd ℂ (wPt y))).re ∧
    |(mEps ε (starRingEnd ℂ (wPt y))).im| ≤ ε / y := by
  have hsq := mEps_arc_sq hy0 hε0 hε1
  have hpos := re_mEps_pos (norm_wbar_le (y := y)) (wbar_ne_one hy0) hε0 hε1
  set v := mEps ε (starRingEnd ℂ (wPt y)) with hv
  have hre := congrArg Complex.re hsq
  have him := congrArg Complex.im hsq
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero,
    zero_add] at hre him
  obtain ⟨b1, b2, b3⟩ := v2_le_aux (v1 := v.re) (v2 := v.im) hy0 hε0 hε1 hpos
    (by calc v.re ^ 2 - v.im ^ 2 = v.re * v.re - v.im * v.im := by ring
          _ = _ := hre
          _ = _ := by ring)
    (by calc 2 * v.re * v.im = v.re * v.im + v.im * v.re := by ring
          _ = _ := him
          _ = _ := by ring)
  refine ⟨hpos, ?_, ?_⟩
  · rw [abs_of_pos b1]; exact b2
  · rw [abs_of_pos b1]; exact b3

/-- **Defect bound for `H_ε = m_ε (1+z²)`.** -/
lemma defectNum_reg_le (hy0 : 0 < y) (hy1 : y < 1) (hε0 : 0 < ε) (hε1 : ε < 1) :
    defectNum (fun z => mEps ε z * (1 + z ^ 2)) y ≤ 25 * ε ^ 2 * y ^ 2 := by
  obtain ⟨a1, a2, a3⟩ := slit_facts hy0 hy1 hε0 hε1
  obtain ⟨b1, b2, b3⟩ := arc_facts hy0 hε0 hε1
  set u := mEps ε (Complex.I * (y : ℂ)) with hu
  set v := mEps ε (starRingEnd ℂ (wPt y)) with hv
  set q : ℝ := 4 * y ^ 2 / (1 + y ^ 2) ^ 2 with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q ≤ 4 * y ^ 2 := by
    rw [hq, div_le_iff₀ (by positivity)]
    nlinarith only [sq_nonneg y, mul_nonneg (sq_nonneg y) (sq_nonneg y),
      mul_nonneg (mul_nonneg (sq_nonneg y) (sq_nonneg y)) (sq_nonneg y)]
  set ρ : ℝ := 1 - y ^ 2 with hρ
  have hy2 : y ^ 2 < 1 := by nlinarith only [hy0, hy1]
  have hρ0 : 0 < ρ := by rw [hρ]; linarith
  have hcore := defect_core (u := u) (v := v) hq0 hρ0 a1 a2 b1.le b2
  have hTim : (u + (q : ℂ) * v).im = u.im + q * v.im := by simp
  have hbound : (u + (q : ℂ) * v).im ^ 2 ≤ (5 * ε * y) ^ 2 := by
    rw [hTim]
    have hv2a : |v.im| ≤ ε / y := b3
    have h1 : |u.im + q * v.im| ≤ 5 * ε * y := by
      calc |u.im + q * v.im| ≤ |u.im| + |q * v.im| := abs_add_le _ _
        _ ≤ ε * y + 4 * y ^ 2 * (ε / y) := by
          rw [abs_mul, abs_of_nonneg hq0]
          gcongr
        _ = 5 * ε * y := by field_simp; ring
    exact sq_le_sq' (by linarith [abs_le.mp h1]) (abs_le.mp h1).2
  unfold defectNum
  rw [edgeSum_reg ε y]
  have hH : ‖(fun z : ℂ => mEps ε z * (1 + z ^ 2)) (Complex.I * (y : ℂ))‖ = ρ * ‖u‖ := by
    have : (1 : ℂ) + (Complex.I * (y : ℂ)) ^ 2 = (ρ : ℂ) := by
      rw [hρ]; push_cast; rw [mul_pow, Complex.I_sq]; ring
    simp only [this, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ0]
    ring
  rw [hH, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ0, Complex.re_ofReal_mul]
  calc max (ρ * ‖u‖) (ρ * ‖u + (q : ℂ) * v‖) - ρ * (u + (q : ℂ) * v).re
      ≤ ρ * (u + (q : ℂ) * v).im ^ 2 := hcore
    _ ≤ 1 * (5 * ε * y) ^ 2 := by
        apply mul_le_mul (by rw [hρ]; linarith [sq_nonneg y]) hbound (sq_nonneg _) (by norm_num)
    _ = 25 * ε ^ 2 * y ^ 2 := by ring

lemma defectInt_reg_le (hy0 : 0 < y) (hy1 : y < 1) (hε0 : 0 < ε) (hε1 : ε < 1) :
    defectInt (fun z => mEps ε z * (1 + z ^ 2)) y ≤ 25 * ε ^ 2 := by
  unfold defectInt
  rw [div_le_iff₀ (by positivity)]
  have := defectNum_reg_le hy0 hy1 hε0 hε1
  linarith only [this]

end

end FormalResearch.ModularBootstrap.FiveTerm

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.defectInt_reg_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.defectInt_reg_le
