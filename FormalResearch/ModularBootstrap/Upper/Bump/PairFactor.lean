module

public import FormalResearch.ModularBootstrap.Upper.Comb.Factors
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The conjugate-pair factor under a change of height (`fw:e3.1`, `fw:e3.2`, `fw:e3.2a`)

Source: `CFT/modular_bootstrap/paper/upper_transfer.tex`, "Quantitative macroscopic bump lemma".

For `ε ∈ [0, 1/2]` and real `y` put `F_ε(y) = (cosh πy - cos πε) / (cosh πy + cos πε)` (`pairF`).

* `blaschkePairQ_eq_pairF` (`fw:e3.1`): `|T_{χ+iε}(x)|² = F_ε(x-χ) F_ε(x+χ)`.
* `pairF_mono` and `blaschkePairQ_mono_eps` (`fw:e3.1`): `F_ε(y)` and the pair modulus increase with `ε`.
* `pairF_le_exp_mul` and `blaschkePairQ_le_exp_mul` (`fw:e3.2a`): for heights between `η₀ ℓ` and `H ℓ`,
  `F_{ε₁}(y) ≤ exp (K ℓ² / (y² + ℓ²)) F_{ε₀}(y)`, with `K` depending only on `(η₀, H)`; the reflected
  factor is absorbed because `(x + χ)² ≥ (x - χ)²` for `x, χ ≥ 0`.
* `pairF_ratio_ge_eventually` and `blaschkePairQ_ratio_ge` (`fw:e3.2`): for `|x - χ| ≤ θ ℓ` with `θ`
  near `1/2` and `ℓ` small, raising the height from `η₀ ℓ` to `H ℓ` multiplies the pair modulus by at least
  `(1 - τ) (H² + 1/4) / (η₀² + 1/4)`; for `η₀ = 1/4` this is `(1 - τ) (16/5) (H² + 1/4)`.

All results are proved unconditionally.
-/

@[expose] public section

open Real Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Bump

open FormalResearch.ModularBootstrap.Upper.Comb

/-! ### 1. The factor `F_ε` and the identity `fw:e3.1` -/

/-- `F_ε(y) = (cosh πy - cos πε) / (cosh πy + cos πε)`. -/
noncomputable def pairF (ε y : ℝ) : ℝ :=
  (Real.cosh (π * y) - Real.cos (π * ε)) / (Real.cosh (π * y) + Real.cos (π * ε))

/-- `F_ε(y) = (sinh²(πy/2) + sin²(πε/2)) / (cosh²(πy/2) - sin²(πε/2))`. -/
lemma pairF_eq (ε y : ℝ) :
    pairF ε y = (Real.sinh (π * y / 2) ^ 2 + Real.sin (π * ε / 2) ^ 2) /
      (Real.cosh (π * y / 2) ^ 2 - Real.sin (π * ε / 2) ^ 2) := by
  unfold pairF
  have e1 : Real.cosh (π * y) = Real.cosh (π * y / 2) ^ 2 + Real.sinh (π * y / 2) ^ 2 := by
    rw [← Real.cosh_two_mul]; ring_nf
  have hc : Real.cosh (π * y / 2) ^ 2 = Real.sinh (π * y / 2) ^ 2 + 1 := Real.cosh_sq _
  have e2 : Real.cos (π * ε) = 1 - 2 * Real.sin (π * ε / 2) ^ 2 := by
    have h1 := Real.cos_two_mul (π * ε / 2)
    have h2 := Real.cos_sq' (π * ε / 2)
    rw [show 2 * (π * ε / 2) = π * ε by ring] at h1
    linarith
  rw [e1, e2]
  have n1 : Real.cosh (π * y / 2) ^ 2 + Real.sinh (π * y / 2) ^ 2 - (1 - 2 * Real.sin (π * ε / 2) ^ 2) =
      2 * (Real.sinh (π * y / 2) ^ 2 + Real.sin (π * ε / 2) ^ 2) := by
    rw [hc]; ring
  have n2 : Real.cosh (π * y / 2) ^ 2 + Real.sinh (π * y / 2) ^ 2 + (1 - 2 * Real.sin (π * ε / 2) ^ 2) =
      2 * (Real.cosh (π * y / 2) ^ 2 - Real.sin (π * ε / 2) ^ 2) := by
    rw [hc]; ring
  rw [n1, n2, mul_div_mul_left _ _ (two_ne_zero)]

lemma pairF_nonneg {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1 / 2) (y : ℝ) : 0 ≤ pairF ε y := by
  have hπ := Real.pi_pos
  have hc0 : 0 ≤ Real.cos (π * ε) :=
    Real.cos_nonneg_of_mem_Icc ⟨by nlinarith, by nlinarith⟩
  have hc1 : Real.cos (π * ε) ≤ 1 := Real.cos_le_one _
  have hy1 : 1 ≤ Real.cosh (π * y) := Real.one_le_cosh _
  unfold pairF
  exact div_nonneg (by linarith) (by linarith)

/-- `fw:e3.1`: for `0 ≤ ε ≤ 1/2`, `F_ε(y)` is increasing in `ε`. -/
lemma pairF_mono {ε₀ ε₁ : ℝ} (h0 : 0 ≤ ε₀) (h01 : ε₀ ≤ ε₁) (h1 : ε₁ ≤ 1 / 2) (y : ℝ) :
    pairF ε₀ y ≤ pairF ε₁ y := by
  have hπ := Real.pi_pos
  have hc : Real.cos (π * ε₁) ≤ Real.cos (π * ε₀) :=
    Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (by nlinarith) (by nlinarith)
  have hc1 : 0 ≤ Real.cos (π * ε₁) :=
    Real.cos_nonneg_of_mem_Icc ⟨by nlinarith, by nlinarith⟩
  have hc0' : Real.cos (π * ε₀) ≤ 1 := Real.cos_le_one _
  have hy1 : 1 ≤ Real.cosh (π * y) := Real.one_le_cosh _
  unfold pairF
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- `fw:e3.1`: the pair modulus is `F_ε(x - χ) F_ε(x + χ)`. -/
theorem blaschkePairQ_eq_pairF (χ ε x : ℝ) :
    blaschkePairQ χ ε x = pairF ε (x - χ) * pairF ε (x + χ) := by
  rw [blaschkePairQ_eq, pairF_eq, pairF_eq, Real.cosh_sq, Real.cosh_sq]

theorem blaschkePairQ_nonneg_of {χ ε x : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1 / 2) :
    0 ≤ blaschkePairQ χ ε x := by
  rw [blaschkePairQ_eq_pairF]
  exact mul_nonneg (pairF_nonneg h0 h1 _) (pairF_nonneg h0 h1 _)

/-- `fw:e3.1`: every conjugate Blaschke pair grows pointwise in modulus when its height grows. -/
theorem blaschkePairQ_mono_eps {χ ε₀ ε₁ : ℝ} (x : ℝ) (h0 : 0 ≤ ε₀) (h01 : ε₀ ≤ ε₁)
    (h1 : ε₁ ≤ 1 / 2) : blaschkePairQ χ ε₀ x ≤ blaschkePairQ χ ε₁ x := by
  rw [blaschkePairQ_eq_pairF, blaschkePairQ_eq_pairF]
  exact mul_le_mul (pairF_mono h0 h01 h1 _) (pairF_mono h0 h01 h1 _)
    (pairF_nonneg h0 (h01.trans h1) _) (pairF_nonneg (h0.trans h01) h1 _)

/-! ### 2. The upper comparison `fw:e3.2a` -/

lemma sq_le_sinh_sq (t : ℝ) : t ^ 2 ≤ Real.sinh t ^ 2 := by
  rcases le_total 0 t with h | h
  · exact pow_le_pow_left₀ h (Real.self_le_sinh_iff.mpr h) 2
  · have h1 : Real.sinh t ≤ t := Real.sinh_le_self_iff.mpr h
    nlinarith

/-- The algebraic splitting of the ratio of two fractions with raised numerator constant. -/
lemma frac_ratio_le {A u₀ u₁ : ℝ} (hA : 0 ≤ A) (hu₀ : 0 < u₀) (h01 : u₀ ≤ u₁) (hu₁ : u₁ ≤ 1 / 2) :
    (A + u₁) / (A + 1 - u₁) ≤
      Real.exp ((u₁ - u₀) * (1 / (A + u₀) + 1 / (A + 1 - u₁))) * ((A + u₀) / (A + 1 - u₀)) := by
  have h1 : 0 < A + u₀ := by linarith
  have h2 : 0 < A + 1 - u₁ := by linarith
  have h3 : 0 < A + 1 - u₀ := by linarith
  have key : (A + u₁) / (A + 1 - u₁) = ((A + u₀) / (A + 1 - u₀)) *
      ((1 + (u₁ - u₀) / (A + u₀)) * (1 + (u₁ - u₀) / (A + 1 - u₁))) := by
    field_simp
    ring
  have hv : 0 ≤ (u₁ - u₀) / (A + u₀) := div_nonneg (by linarith) h1.le
  have hw : 0 ≤ (u₁ - u₀) / (A + 1 - u₁) := div_nonneg (by linarith) h2.le
  have e1 : 1 + (u₁ - u₀) / (A + u₀) ≤ Real.exp ((u₁ - u₀) / (A + u₀)) := by
    linarith [Real.add_one_le_exp ((u₁ - u₀) / (A + u₀))]
  have e2 : 1 + (u₁ - u₀) / (A + 1 - u₁) ≤ Real.exp ((u₁ - u₀) / (A + 1 - u₁)) := by
    linarith [Real.add_one_le_exp ((u₁ - u₀) / (A + 1 - u₁))]
  have hexp : (1 + (u₁ - u₀) / (A + u₀)) * (1 + (u₁ - u₀) / (A + 1 - u₁)) ≤
      Real.exp ((u₁ - u₀) * (1 / (A + u₀) + 1 / (A + 1 - u₁))) := by
    calc (1 + (u₁ - u₀) / (A + u₀)) * (1 + (u₁ - u₀) / (A + 1 - u₁))
        ≤ Real.exp ((u₁ - u₀) / (A + u₀)) * Real.exp ((u₁ - u₀) / (A + 1 - u₁)) :=
          mul_le_mul e1 e2 (by linarith) (Real.exp_pos _).le
      _ = Real.exp ((u₁ - u₀) / (A + u₀) + (u₁ - u₀) / (A + 1 - u₁)) := (Real.exp_add _ _).symm
      _ = _ := by congr 1; ring
  rw [key, mul_comm]
  exact mul_le_mul_of_nonneg_right hexp (by positivity)

/-- The constant of `fw:e3.2a`. -/
noncomputable def pairK (η₀ H : ℝ) : ℝ := (π * H / 2) ^ 2 * (1 / min 1 (η₀ ^ 2) + 2)

lemma pairK_nonneg (η₀ H : ℝ) : 0 ≤ pairK η₀ H := by
  unfold pairK
  positivity

/-- Elementary bounds for the `sin²` factors: with `ε₀ ≥ η₀ ℓ`, `ε₁ ≤ H ℓ ≤ 1/2`. -/
lemma sin_sq_bounds {η₀ H ℓ ε₀ ε₁ : ℝ} (hη₀ : 0 < η₀) (hℓ : 0 < ℓ) (hε₀ : η₀ * ℓ ≤ ε₀)
    (h01 : ε₀ ≤ ε₁) (hε₁ : ε₁ ≤ H * ℓ) (hHℓ : H * ℓ ≤ 1 / 2) :
    (η₀ * ℓ) ^ 2 ≤ Real.sin (π * ε₀ / 2) ^ 2 ∧ Real.sin (π * ε₀ / 2) ^ 2 ≤ Real.sin (π * ε₁ / 2) ^ 2 ∧
      Real.sin (π * ε₁ / 2) ^ 2 ≤ 1 / 2 ∧ Real.sin (π * ε₁ / 2) ^ 2 ≤ (π * H * ℓ / 2) ^ 2 := by
  have hπ := Real.pi_pos
  have hε₀0 : 0 < ε₀ := lt_of_lt_of_le (by positivity) hε₀
  have hε₁1 : ε₁ ≤ 1 / 2 := hε₁.trans hHℓ
  have hs0 : 0 ≤ Real.sin (π * ε₀ / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith)
  have hs1 : 0 ≤ Real.sin (π * ε₁ / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith) (by nlinarith)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := Real.mul_le_sin (x := π * ε₀ / 2) (by positivity) (by nlinarith)
    have h' : ε₀ ≤ Real.sin (π * ε₀ / 2) := by
      have : 2 / π * (π * ε₀ / 2) = ε₀ := by field_simp
      linarith
    have : η₀ * ℓ ≤ Real.sin (π * ε₀ / 2) := hε₀.trans h'
    exact pow_le_pow_left₀ (by positivity) this 2
  · exact pow_le_pow_left₀ hs0
      (Real.sin_le_sin_of_le_of_le_pi_div_two (by nlinarith) (by nlinarith) (by nlinarith)) 2
  · have h : Real.sin (π * ε₁ / 2) ≤ Real.sin (π / 4) :=
      Real.sin_le_sin_of_le_of_le_pi_div_two (by nlinarith) (by nlinarith) (by nlinarith)
    rw [Real.sin_pi_div_four] at h
    have := pow_le_pow_left₀ hs1 h 2
    rw [div_pow, Real.sq_sqrt (by norm_num)] at this
    linarith
  · have h : Real.sin (π * ε₁ / 2) ≤ π * ε₁ / 2 := Real.sin_le (by nlinarith)
    have h2 : π * ε₁ / 2 ≤ π * H * ℓ / 2 := by nlinarith
    exact pow_le_pow_left₀ hs1 (h.trans h2) 2

/-- **`fw:e3.2a`, one factor.**  For `η₀ ℓ ≤ ε₀ ≤ ε₁ ≤ H ℓ`, `H ℓ ≤ 1/2`, `0 < ℓ ≤ 1`:
`F_{ε₁}(y) ≤ exp (K ℓ² / (y² + ℓ²)) F_{ε₀}(y)`. -/
theorem pairF_le_exp_mul {η₀ H ℓ ε₀ ε₁ : ℝ} (hη₀ : 0 < η₀) (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1)
    (hε₀ : η₀ * ℓ ≤ ε₀) (h01 : ε₀ ≤ ε₁) (hε₁ : ε₁ ≤ H * ℓ) (hHℓ : H * ℓ ≤ 1 / 2) (y : ℝ) :
    pairF ε₁ y ≤ Real.exp (pairK η₀ H * ℓ ^ 2 / (y ^ 2 + ℓ ^ 2)) * pairF ε₀ y := by
  have hπ := Real.pi_pos
  have hπ2 : (2 : ℝ) ≤ π := by linarith [Real.pi_gt_three]
  obtain ⟨hu0lb, h01', hu1, hu1ub⟩ := sin_sq_bounds hη₀ hℓ hε₀ h01 hε₁ hHℓ
  set A := Real.sinh (π * y / 2) ^ 2 with hA
  set u₀ := Real.sin (π * ε₀ / 2) ^ 2 with hu₀
  set u₁ := Real.sin (π * ε₁ / 2) ^ 2 with hu₁def
  have hu0pos : 0 < u₀ := lt_of_lt_of_le (by positivity) hu0lb
  have hAy : (π * y / 2) ^ 2 ≤ A := sq_le_sinh_sq _
  have hy2 : y ^ 2 ≤ (π * y / 2) ^ 2 := by
    have : y ^ 2 * (π / 2) ^ 2 = (π * y / 2) ^ 2 := by ring
    nlinarith [sq_nonneg y, sq_nonneg (π / 2 - 1)]
  have hA0 : 0 ≤ A := by positivity
  rw [pairF_eq, pairF_eq, Real.cosh_sq]
  refine le_trans (frac_ratio_le hA0 hu0pos h01' hu1) ?_
  refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) ?_
  · -- the exponent
    set m := min 1 (η₀ ^ 2) with hm
    have hm0 : 0 < m := lt_min one_pos (by positivity)
    have hm1 : m ≤ 1 := min_le_left _ _
    have hm2 : m ≤ η₀ ^ 2 := min_le_right _ _
    have hyℓ : 0 < y ^ 2 + ℓ ^ 2 := by positivity
    have hd1 : m * (y ^ 2 + ℓ ^ 2) ≤ A + u₀ := by
      have : m * (y ^ 2 + ℓ ^ 2) ≤ y ^ 2 + (η₀ * ℓ) ^ 2 := by
        have h1 : m * y ^ 2 ≤ y ^ 2 := by nlinarith [sq_nonneg y]
        have h2 : m * ℓ ^ 2 ≤ (η₀ * ℓ) ^ 2 := by
          rw [mul_pow]; exact mul_le_mul_of_nonneg_right hm2 (sq_nonneg _)
        nlinarith
      linarith
    have hd2 : (y ^ 2 + ℓ ^ 2) / 2 ≤ A + 1 - u₁ := by
      have : ℓ ^ 2 ≤ 1 := by nlinarith
      nlinarith
    have hpos1 : 0 < A + u₀ := by linarith
    have hpos2 : 0 < A + 1 - u₁ := by linarith
    have hb1 : 1 / (A + u₀) ≤ 1 / (m * (y ^ 2 + ℓ ^ 2)) :=
      one_div_le_one_div_of_le (by positivity) hd1
    have hb2 : 1 / (A + 1 - u₁) ≤ 2 / (y ^ 2 + ℓ ^ 2) := by
      rw [div_le_div_iff₀ hpos2 hyℓ]
      nlinarith
    have hnum : u₁ - u₀ ≤ (π * H * ℓ / 2) ^ 2 := by linarith
    have hnum0 : 0 ≤ u₁ - u₀ := by linarith
    calc (u₁ - u₀) * (1 / (A + u₀) + 1 / (A + 1 - u₁))
        ≤ (π * H * ℓ / 2) ^ 2 * (1 / (m * (y ^ 2 + ℓ ^ 2)) + 2 / (y ^ 2 + ℓ ^ 2)) :=
          mul_le_mul hnum (add_le_add hb1 hb2) (by positivity) (by positivity)
      _ = pairK η₀ H * ℓ ^ 2 / (y ^ 2 + ℓ ^ 2) := by
          unfold pairK
          rw [← hm]
          field_simp
  · exact div_nonneg (by positivity) (by linarith)

/-- **`fw:e3.2a`, pair modulus.**  For `x, χ ≥ 0` and heights as in `pairF_le_exp_mul`,
`Q_{ε₁} ≤ exp (2 K ℓ² / ((x - χ)² + ℓ²)) Q_{ε₀}`. -/
theorem blaschkePairQ_le_exp_mul {η₀ H ℓ ε₀ ε₁ χ x : ℝ} (hη₀ : 0 < η₀) (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1)
    (hε₀ : η₀ * ℓ ≤ ε₀) (h01 : ε₀ ≤ ε₁) (hε₁ : ε₁ ≤ H * ℓ) (hHℓ : H * ℓ ≤ 1 / 2)
    (hχ : 0 ≤ χ) (hx : 0 ≤ x) :
    blaschkePairQ χ ε₁ x ≤
      Real.exp (2 * pairK η₀ H * ℓ ^ 2 / ((x - χ) ^ 2 + ℓ ^ 2)) * blaschkePairQ χ ε₀ x := by
  have hε₀0 : 0 ≤ ε₀ := (mul_pos hη₀ hℓ).le.trans hε₀
  have hε₁1 : ε₁ ≤ 1 / 2 := hε₁.trans hHℓ
  have a1 := pairF_le_exp_mul hη₀ hℓ hℓ1 hε₀ h01 hε₁ hHℓ (x - χ)
  have a2 := pairF_le_exp_mul hη₀ hℓ hℓ1 hε₀ h01 hε₁ hHℓ (x + χ)
  have hK := pairK_nonneg η₀ H
  have hle : (x - χ) ^ 2 ≤ (x + χ) ^ 2 := by nlinarith
  have hd1 : 0 < (x - χ) ^ 2 + ℓ ^ 2 := by positivity
  have hexp2 : pairK η₀ H * ℓ ^ 2 / ((x + χ) ^ 2 + ℓ ^ 2) ≤
      pairK η₀ H * ℓ ^ 2 / ((x - χ) ^ 2 + ℓ ^ 2) :=
    div_le_div_of_nonneg_left (by positivity) hd1 (by linarith)
  have b2 : pairF ε₁ (x + χ) ≤ Real.exp (pairK η₀ H * ℓ ^ 2 / ((x - χ) ^ 2 + ℓ ^ 2)) *
      pairF ε₀ (x + χ) :=
    a2.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hexp2)
      (pairF_nonneg hε₀0 (h01.trans hε₁1) _))
  rw [blaschkePairQ_eq_pairF, blaschkePairQ_eq_pairF]
  calc pairF ε₁ (x - χ) * pairF ε₁ (x + χ)
      ≤ (Real.exp (pairK η₀ H * ℓ ^ 2 / ((x - χ) ^ 2 + ℓ ^ 2)) * pairF ε₀ (x - χ)) *
        (Real.exp (pairK η₀ H * ℓ ^ 2 / ((x - χ) ^ 2 + ℓ ^ 2)) * pairF ε₀ (x + χ)) :=
        mul_le_mul a1 b2 (pairF_nonneg (hε₀0.trans h01) hε₁1 _)
          (mul_nonneg (Real.exp_pos _).le (pairF_nonneg hε₀0 (h01.trans hε₁1) _))
    _ = Real.exp (2 * pairK η₀ H * ℓ ^ 2 / ((x - χ) ^ 2 + ℓ ^ 2)) *
        (pairF ε₀ (x - χ) * pairF ε₀ (x + χ)) := by
        rw [show 2 * pairK η₀ H * ℓ ^ 2 / ((x - χ) ^ 2 + ℓ ^ 2) =
          pairK η₀ H * ℓ ^ 2 / ((x - χ) ^ 2 + ℓ ^ 2) + pairK η₀ H * ℓ ^ 2 / ((x - χ) ^ 2 + ℓ ^ 2)
          by ring, Real.exp_add]
        ring

/-! ### 3. The lower comparison `fw:e3.2` at the nearest site -/

/-- The limit function of `fw:e3.2` in the variables `θ` (`|y| ≤ θ ℓ`) and `t = π ℓ / 2`. -/
noncomputable def nearGain (η₀ H θ t : ℝ) : ℝ :=
  1 + (H ^ 2 * (1 - H ^ 2 * t ^ 2 / 3) - η₀ ^ 2) / (θ ^ 2 * Real.exp (θ ^ 2 * t ^ 2) + η₀ ^ 2)

lemma sinh_sq_le_of_abs_le {z s : ℝ} (hz : |z| ≤ s) :
    Real.sinh z ^ 2 ≤ s ^ 2 * Real.exp (s ^ 2) := by
  have hz2 : z ^ 2 ≤ s ^ 2 := by
    have := sq_le_sq' (abs_le.mp hz).1 (abs_le.mp hz).2
    simpa using this
  have hch : Real.cosh z ≤ Real.exp (z ^ 2 / 2) := Real.cosh_le_exp_half_sq z
  have hch2 : Real.cosh z ^ 2 ≤ Real.exp (z ^ 2) := by
    calc Real.cosh z ^ 2 ≤ Real.exp (z ^ 2 / 2) ^ 2 :=
          pow_le_pow_left₀ (Real.cosh_pos z).le hch 2
      _ = Real.exp (z ^ 2) := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have h1 : Real.sinh z ^ 2 = Real.cosh z ^ 2 - 1 := by linarith [Real.cosh_sq z]
  have h2 : Real.exp (z ^ 2) - 1 ≤ z ^ 2 * Real.exp (z ^ 2) := by
    have := Real.add_one_le_exp (-(z ^ 2))
    have h3 : Real.exp (-(z ^ 2)) * Real.exp (z ^ 2) = 1 := by
      rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos (z ^ 2)]
  calc Real.sinh z ^ 2 ≤ z ^ 2 * Real.exp (z ^ 2) := by linarith
    _ ≤ s ^ 2 * Real.exp (s ^ 2) :=
      mul_le_mul hz2 (Real.exp_le_exp.mpr hz2) (Real.exp_pos _).le (sq_nonneg _)

/-- The algebraic core of `fw:e3.2`. -/
lemma frac_ratio_ge {A u₀ u₁ g : ℝ} (hA : 0 ≤ A) (hu₀ : 0 < u₀) (h01 : u₀ ≤ u₁) (hu₁ : u₁ ≤ 1 / 2)
    (hg : g ≤ 1 + (u₁ - u₀) / (A + u₀)) :
    g * ((A + u₀) / (A + 1 - u₀)) ≤ (A + u₁) / (A + 1 - u₁) := by
  have h1 : 0 < A + u₀ := by linarith
  have h2 : 0 < A + 1 - u₁ := by linarith
  have h3 : 0 < A + 1 - u₀ := by linarith
  have key : (A + u₁) / (A + 1 - u₁) = ((A + u₀) / (A + 1 - u₀)) *
      ((1 + (u₁ - u₀) / (A + u₀)) * (1 + (u₁ - u₀) / (A + 1 - u₁))) := by
    field_simp
    ring
  have hvv : 0 ≤ (u₁ - u₀) / (A + u₀) := div_nonneg (by linarith) h1.le
  have hww : 0 ≤ (u₁ - u₀) / (A + 1 - u₁) := div_nonneg (by linarith) h2.le
  have hF0 : 0 ≤ (A + u₀) / (A + 1 - u₀) := by positivity
  rw [key]
  calc g * ((A + u₀) / (A + 1 - u₀))
      ≤ (1 + (u₁ - u₀) / (A + u₀)) * ((A + u₀) / (A + 1 - u₀)) :=
        mul_le_mul_of_nonneg_right hg hF0
    _ ≤ (1 + (u₁ - u₀) / (A + u₀)) * (1 + (u₁ - u₀) / (A + 1 - u₁)) *
          ((A + u₀) / (A + 1 - u₀)) := by
        apply mul_le_mul_of_nonneg_right _ hF0
        nlinarith
    _ = ((A + u₀) / (A + 1 - u₀)) *
      ((1 + (u₁ - u₀) / (A + u₀)) * (1 + (u₁ - u₀) / (A + 1 - u₁))) := by ring

/-- The gain is at most `1 + (u₁ - u₀) / (A + u₀)` once `A`, `u₀`, `u₁` are controlled. -/
lemma nearGain_le_aux {η₀ H θ t A u₀ u₁ : ℝ} (hη₀ : 0 < η₀)
    (hA0 : 0 ≤ A) (hu0pos : 0 < u₀) (h01 : u₀ ≤ u₁)
    (hAup : A ≤ (θ * t) ^ 2 * Real.exp ((θ * t) ^ 2)) (hu0up : u₀ ≤ (η₀ * t) ^ 2)
    (hu1lb : (H * t) ^ 2 * (1 - H ^ 2 * t ^ 2 / 3) ≤ u₁) :
    nearGain η₀ H θ t ≤ 1 + (u₁ - u₀) / (A + u₀) := by
  unfold nearGain
  have hDd : 0 < θ ^ 2 * Real.exp (θ ^ 2 * t ^ 2) + η₀ ^ 2 := by positivity
  have hpos : 0 < A + u₀ := by linarith
  set N := H ^ 2 * (1 - H ^ 2 * t ^ 2 / 3) - η₀ ^ 2 with hN
  set Dd := θ ^ 2 * Real.exp (θ ^ 2 * t ^ 2) + η₀ ^ 2 with hDdd
  have hbound : A + u₀ ≤ t ^ 2 * Dd := by
    have e : (θ * t) ^ 2 * Real.exp ((θ * t) ^ 2) = t ^ 2 * (θ ^ 2 * Real.exp (θ ^ 2 * t ^ 2)) := by
      rw [mul_pow]; ring
    have e2 : (η₀ * t) ^ 2 = t ^ 2 * η₀ ^ 2 := by ring
    have : t ^ 2 * Dd = t ^ 2 * (θ ^ 2 * Real.exp (θ ^ 2 * t ^ 2)) + t ^ 2 * η₀ ^ 2 := by
      rw [hDdd]; ring
    linarith
  have hnum : t ^ 2 * N ≤ u₁ - u₀ := by
    have : t ^ 2 * N = (H * t) ^ 2 * (1 - H ^ 2 * t ^ 2 / 3) - (η₀ * t) ^ 2 := by
      rw [hN]; ring
    linarith
  suffices h : N / Dd ≤ (u₁ - u₀) / (A + u₀) by linarith
  rcases le_or_gt 0 N with hN0 | hN0
  · rw [div_le_div_iff₀ hDd hpos]
    have h1 : N * (A + u₀) ≤ N * (t ^ 2 * Dd) := mul_le_mul_of_nonneg_left hbound hN0
    have h2 : (t ^ 2 * N) * Dd ≤ (u₁ - u₀) * Dd := mul_le_mul_of_nonneg_right hnum hDd.le
    nlinarith
  · have h1 : N / Dd < 0 := div_neg_of_neg_of_pos hN0 hDd
    have h2 : 0 ≤ (u₁ - u₀) / (A + u₀) := div_nonneg (by linarith) hpos.le
    linarith

/-- **`fw:e3.2`, one factor.**  For `0 < η₀ ≤ H`, `0 < ℓ`, `H ℓ ≤ 1/2`, `|y| ≤ θ ℓ`:
`nearGain η₀ H θ (π ℓ / 2) · F_{η₀ ℓ}(y) ≤ F_{H ℓ}(y)`. -/
theorem pairF_ratio_ge {η₀ H ℓ y θ : ℝ} (hη₀ : 0 < η₀) (hηH : η₀ ≤ H) (hℓ : 0 < ℓ)
    (hHℓ : H * ℓ ≤ 1 / 2) (hy : |y| ≤ θ * ℓ) :
    nearGain η₀ H θ (π * ℓ / 2) * pairF (η₀ * ℓ) y ≤ pairF (H * ℓ) y := by
  have hπ := Real.pi_pos
  have hH0 : 0 < H := lt_of_lt_of_le hη₀ hηH
  have h01 : η₀ * ℓ ≤ H * ℓ := mul_le_mul_of_nonneg_right hηH hℓ.le
  obtain ⟨hu0lb, h01', hu1, hu1ub⟩ := sin_sq_bounds hη₀ hℓ le_rfl h01 le_rfl hHℓ
  set t := π * ℓ / 2 with ht
  have ht0 : 0 < t := by positivity
  set A := Real.sinh (π * y / 2) ^ 2 with hA
  set u₀ := Real.sin (π * (η₀ * ℓ) / 2) ^ 2 with hu₀
  set u₁ := Real.sin (π * (H * ℓ) / 2) ^ 2 with hu₁def
  have hu0pos : 0 < u₀ := lt_of_lt_of_le (by positivity) hu0lb
  have hA0 : 0 ≤ A := by positivity
  have hAup : A ≤ (θ * t) ^ 2 * Real.exp ((θ * t) ^ 2) := by
    refine sinh_sq_le_of_abs_le ?_
    have : |π * y / 2| = π / 2 * |y| := by
      rw [abs_div, abs_mul, abs_of_pos hπ, abs_two]; ring
    rw [this, ht]
    nlinarith [abs_nonneg y]
  have hu0up : u₀ ≤ (η₀ * t) ^ 2 := by
    have h : Real.sin (π * (η₀ * ℓ) / 2) ≤ π * (η₀ * ℓ) / 2 := Real.sin_le (by positivity)
    have hs0 : 0 ≤ Real.sin (π * (η₀ * ℓ) / 2) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith)
    have := pow_le_pow_left₀ hs0 h 2
    calc u₀ ≤ (π * (η₀ * ℓ) / 2) ^ 2 := this
      _ = (η₀ * t) ^ 2 := by rw [ht]; ring
  have hu1lb : (H * t) ^ 2 * (1 - H ^ 2 * t ^ 2 / 3) ≤ u₁ := by
    set x := H * t with hx
    have hx0 : 0 < x := by positivity
    have hx' : x = π * (H * ℓ) / 2 := by rw [hx, ht]; ring
    have hx1 : x ≤ 1 := by
      rw [hx']
      nlinarith [Real.pi_le_four, mul_le_mul_of_nonneg_left hHℓ hπ.le]
    have hs : x - x ^ 3 / 6 < Real.sin x := Real.sin_gt_sub_cube hx0
    have hsin : Real.sin (π * (H * ℓ) / 2) = Real.sin x := by rw [hx']
    have hpos : 0 ≤ x - x ^ 3 / 6 := by nlinarith [sq_nonneg x]
    have hsq : (x - x ^ 3 / 6) ^ 2 ≤ u₁ := by
      rw [hu₁def, hsin]
      exact pow_le_pow_left₀ hpos hs.le 2
    have h3 : x ^ 2 * (1 - x ^ 2 / 3) ≤ (x - x ^ 3 / 6) ^ 2 := by
      nlinarith [sq_nonneg (x ^ 2), sq_nonneg x]
    have e : (H * t) ^ 2 * (1 - H ^ 2 * t ^ 2 / 3) = x ^ 2 * (1 - x ^ 2 / 3) := by
      rw [hx]; ring
    rw [e]
    linarith
  have hg := nearGain_le_aux hη₀ hA0 hu0pos h01' hAup hu0up hu1lb
  rw [pairF_eq, pairF_eq, Real.cosh_sq]
  exact frac_ratio_ge hA0 hu0pos h01' hu1 hg

/-- The limit of the gain is `(H² + 1/4)/(η₀² + 1/4)`; for `η₀ = 1/4` this is `(16/5)(H² + 1/4)`. -/
lemma nearGain_limit (η₀ H : ℝ) :
    nearGain η₀ H (1 / 2) 0 = (H ^ 2 + 1 / 4) / (η₀ ^ 2 + 1 / 4) := by
  unfold nearGain
  simp
  have : (1 / 4 : ℝ) + η₀ ^ 2 ≠ 0 := by positivity
  field_simp
  ring

lemma continuous_nearGain {η₀ H : ℝ} (hη₀ : 0 < η₀) :
    Continuous (fun p : ℝ × ℝ => nearGain η₀ H p.1 p.2) := by
  unfold nearGain
  refine continuous_const.add (Continuous.div ?_ ?_ fun p => ?_)
  · fun_prop
  · fun_prop
  · positivity

/-- **`fw:e3.2`, uniform form.**  For `0 < η₀ ≤ H` and `τ > 0` there is `δ > 0` such that for `θ ∈ [1/2, 1/2 + δ]`,
`0 < ℓ ≤ δ`, `|y| ≤ θ ℓ`: `(1 - τ) (H² + 1/4)/(η₀² + 1/4) F_{η₀ ℓ}(y) ≤ F_{H ℓ}(y)`. -/
theorem pairF_ratio_ge_eventually {η₀ H : ℝ} (hη₀ : 0 < η₀) (hηH : η₀ ≤ H) {τ : ℝ} (hτ : 0 < τ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ θ ℓ y : ℝ, 1 / 2 ≤ θ → θ ≤ 1 / 2 + δ → 0 < ℓ → ℓ ≤ δ → |y| ≤ θ * ℓ →
      (1 - τ) * ((H ^ 2 + 1 / 4) / (η₀ ^ 2 + 1 / 4)) * pairF (η₀ * ℓ) y ≤ pairF (H * ℓ) y := by
  have hπ := Real.pi_pos
  have hH0 : 0 < H := lt_of_lt_of_le hη₀ hηH
  set g := (H ^ 2 + 1 / 4) / (η₀ ^ 2 + 1 / 4) with hg
  have hgpos : 0 < g := by positivity
  have hcont := (continuous_nearGain (H := H) hη₀).continuousAt (x := ((1 : ℝ) / 2, (0 : ℝ)))
  have hlim : nearGain η₀ H (1 / 2) 0 = g := nearGain_limit η₀ H
  have hev : ∀ᶠ p : ℝ × ℝ in 𝓝 ((1 : ℝ) / 2, (0 : ℝ)), (1 - τ) * g < nearGain η₀ H p.1 p.2 := by
    have : (1 - τ) * g < nearGain η₀ H ((1 : ℝ) / 2) 0 := by
      rw [hlim]; nlinarith
    exact hcont.eventually (lt_mem_nhds this)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨min (min (ε / 2) (1 / (2 * H))) (ε / π), ?_, ?_⟩
  · have : 0 < 1 / (2 * H) := by positivity
    exact lt_min (lt_min (by positivity) this) (by positivity)
  intro θ ℓ y hθ1 hθ2 hℓ hℓδ hy
  have hδ1 : min (min (ε / 2) (1 / (2 * H))) (ε / π) ≤ ε / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hδ2 : min (min (ε / 2) (1 / (2 * H))) (ε / π) ≤ 1 / (2 * H) :=
    (min_le_left _ _).trans (min_le_right _ _)
  have hδ3 : min (min (ε / 2) (1 / (2 * H))) (ε / π) ≤ ε / π := min_le_right _ _
  have hHℓ : H * ℓ ≤ 1 / 2 := by
    have := (hℓδ.trans hδ2)
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  have ht : π * ℓ / 2 < ε := by
    have h1 : ℓ ≤ ε / π := hℓδ.trans hδ3
    rw [le_div_iff₀ hπ] at h1
    nlinarith
  have hdist : dist (θ, π * ℓ / 2) ((1 : ℝ) / 2, (0 : ℝ)) < ε := by
    rw [Prod.dist_eq]
    refine max_lt ?_ ?_
    · rw [Real.dist_eq, abs_lt]
      constructor <;> linarith
    · rw [Real.dist_eq, abs_lt]
      constructor <;> nlinarith
  have hgain := hball hdist
  simp only at hgain
  have hF0 : 0 ≤ pairF (η₀ * ℓ) y := pairF_nonneg (by positivity) (by nlinarith) y
  have hmain := pairF_ratio_ge hη₀ hηH hℓ hHℓ hy
  calc (1 - τ) * g * pairF (η₀ * ℓ) y ≤ nearGain η₀ H θ (π * ℓ / 2) * pairF (η₀ * ℓ) y :=
        mul_le_mul_of_nonneg_right hgain.le hF0
    _ ≤ pairF (H * ℓ) y := hmain

/-- **`fw:e3.2`, pair modulus at the nearest site.**  With `δ` as in `pairF_ratio_ge_eventually`, for
`x, χ ≥ 0` with `|x - χ| ≤ θ ℓ`: `(1 - τ) g Q_{η₀ ℓ} ≤ Q_{H ℓ}`, `g = (H² + 1/4)/(η₀² + 1/4)`. -/
theorem blaschkePairQ_ratio_ge {η₀ H : ℝ} (hη₀ : 0 < η₀) (hηH : η₀ ≤ H) {τ : ℝ} (hτ : 0 < τ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ θ ℓ χ x : ℝ, 1 / 2 ≤ θ → θ ≤ 1 / 2 + δ → 0 < ℓ → ℓ ≤ δ →
      |x - χ| ≤ θ * ℓ → 0 ≤ χ → 0 ≤ x → H * ℓ ≤ 1 / 2 →
      (1 - τ) * ((H ^ 2 + 1 / 4) / (η₀ ^ 2 + 1 / 4)) * blaschkePairQ χ (η₀ * ℓ) x ≤
        blaschkePairQ χ (H * ℓ) x := by
  obtain ⟨δ, hδ, h⟩ := pairF_ratio_ge_eventually hη₀ hηH hτ
  refine ⟨δ, hδ, fun θ ℓ χ x hθ1 hθ2 hℓ hℓδ hxχ hχ hx hHℓ => ?_⟩
  have h1 := h θ ℓ (x - χ) hθ1 hθ2 hℓ hℓδ hxχ
  have hε0 : 0 ≤ η₀ * ℓ := by positivity
  have h01 : η₀ * ℓ ≤ H * ℓ := mul_le_mul_of_nonneg_right hηH hℓ.le
  have h2 : pairF (η₀ * ℓ) (x + χ) ≤ pairF (H * ℓ) (x + χ) := pairF_mono hε0 h01 hHℓ _
  have hpos : 0 ≤ pairF (η₀ * ℓ) (x + χ) := pairF_nonneg hε0 (h01.trans hHℓ) _
  have hQ0 : 0 ≤ blaschkePairQ χ (η₀ * ℓ) x :=
    blaschkePairQ_nonneg_of hε0 (h01.trans hHℓ)
  have hQ1 : 0 ≤ blaschkePairQ χ (H * ℓ) x :=
    blaschkePairQ_nonneg_of (hε0.trans h01) hHℓ
  rcases lt_or_ge ((1 - τ) * ((H ^ 2 + 1 / 4) / (η₀ ^ 2 + 1 / 4))) 0 with hneg | hg
  · exact le_trans (mul_nonpos_of_nonpos_of_nonneg hneg.le hQ0) hQ1
  rw [blaschkePairQ_eq_pairF, blaschkePairQ_eq_pairF]
  have hF0 : 0 ≤ pairF (η₀ * ℓ) (x - χ) := pairF_nonneg hε0 (h01.trans hHℓ) _
  calc (1 - τ) * ((H ^ 2 + 1 / 4) / (η₀ ^ 2 + 1 / 4)) *
        (pairF (η₀ * ℓ) (x - χ) * pairF (η₀ * ℓ) (x + χ))
      = ((1 - τ) * ((H ^ 2 + 1 / 4) / (η₀ ^ 2 + 1 / 4)) * pairF (η₀ * ℓ) (x - χ)) *
        pairF (η₀ * ℓ) (x + χ) := by ring
    _ ≤ pairF (H * ℓ) (x - χ) * pairF (H * ℓ) (x + χ) :=
        mul_le_mul h1 h2 hpos ((mul_nonneg hg hF0).trans h1)

/-- info: 'FormalResearch.ModularBootstrap.Upper.Bump.blaschkePairQ_eq_pairF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms blaschkePairQ_eq_pairF

/-- info: 'FormalResearch.ModularBootstrap.Upper.Bump.blaschkePairQ_mono_eps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms blaschkePairQ_mono_eps

/-- info: 'FormalResearch.ModularBootstrap.Upper.Bump.blaschkePairQ_le_exp_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms blaschkePairQ_le_exp_mul

/-- info: 'FormalResearch.ModularBootstrap.Upper.Bump.blaschkePairQ_ratio_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms blaschkePairQ_ratio_ge

end FormalResearch.ModularBootstrap.Upper.Bump
