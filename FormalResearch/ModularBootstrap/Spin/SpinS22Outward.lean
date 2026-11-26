module

public import FormalResearch.ModularBootstrap.Spin.SpinS22Strip
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Lemma S2.2 (`spinnotes:S22`): outward `L¹` bound, inward unboundedness, and assembly

Proves the remaining parts of **Lemma S2.2** (`spinning_foundations.tex`, lines 188–248) and
assembles `theorem spinS22 : SpinS22`:

* `spinWc_mono_abs`: monotonicity of `w_c(x)` in `|x|` for `a ≥ 2`.
* `integrable_and_integral_spinDeltaA_wc`: outward `L¹` integrability and
  `∬ |Δ_a G| w_c ⊗ w_c ≤ (1 + λ⁻¹)² M_2[Φ]`.
* `spinDa_unbounded`: unboundedness of `‖D_a G‖_{L¹(w_c ⊗ w_c)} / M_2[Φ]` on
  `\overline{\mathcal A}_{\rm spin}` via the Gaussian family
  `Φ_s(r) = e^{-π s |r|²} - s⁻¹ e^{-π |r|² / s}` (`s ↓ 0`).
* `spinS22 : SpinS22`: full assembly of Lemma S2.2.
-/

@[expose] public section

open Real Complex MeasureTheory Filter Topology Set
open scoped Real FourierTransform InnerProductSpace

namespace FormalResearch.ModularBootstrap.Spin

/-! ### Helper identities for `spinGamma` and `spinLambda` -/

private lemma spinGamma_pos' {a : ℝ} (ha : 2 < a) : 0 < spinGamma a := by
  unfold spinGamma
  refine Real.sqrt_pos.mpr ?_
  have hdiv : 2 / a < 1 := (div_lt_one (by linarith)).mpr ha
  linarith

private lemma spinGamma_sq' {a : ℝ} (ha : 2 ≤ a) : spinGamma a ^ 2 = (a - 2) / a := by
  unfold spinGamma
  have h1 : 1 - 2 / a = (a - 2) / a := by field_simp [(by linarith : a ≠ 0)]
  rw [h1]
  exact Real.sq_sqrt (div_nonneg (by linarith) (by linarith))

private lemma spinGamma_lt_one' {a : ℝ} (ha : 2 < a) : spinGamma a < 1 := by
  unfold spinGamma
  have hpos : 0 < 2 / a := div_pos two_pos (by linarith)
  have hlt : 2 / a < 1 := (div_lt_one (by linarith)).mpr ha
  calc Real.sqrt (1 - 2 / a) < Real.sqrt 1 := Real.sqrt_lt_sqrt (by linarith) (by linarith)
    _ = 1 := Real.sqrt_one

private lemma spinLambda_ge_one' {a : ℝ} (ha : 2 < a) : 1 ≤ spinLambda a := by
  unfold spinLambda
  exact (one_le_inv₀ (spinGamma_pos' ha)).mpr (spinGamma_lt_one' ha).le

private lemma spinGamma_mul_spinLambda' {a : ℝ} (ha : 2 < a) : spinGamma a * spinLambda a = 1 := by
  unfold spinLambda
  exact mul_inv_cancel₀ (spinGamma_pos' ha).ne'

private lemma spinDeltaA_expand {a : ℝ} (ha : 2 < a) (Φ : ℝ × ℝ → ℝ) (xL xR : ℝ) :
    spinDeltaA a Φ xL xR =
      spinG a Φ (spinLambda a * xL) (spinLambda a * xR) -
        spinG a Φ xL (spinLambda a * xR) -
        spinG a Φ (spinLambda a * xL) xR +
        spinG a Φ xL xR := by
  unfold spinDeltaA spinDa
  have hgl : spinGamma a * spinLambda a = 1 := spinGamma_mul_spinLambda' ha
  rw [← mul_assoc, ← mul_assoc, hgl, one_mul, one_mul]

/-! ### Part 1: Monotonicity of `w_c` and outward `L¹` bound -/

lemma spinWc_abs (a x : ℝ) : spinWc a |x| = spinWc a x := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
  · rw [abs_of_nonpos hx, spinWc_even]

lemma spinWc_mono_abs {a : ℝ} (ha : 2 ≤ a) {x y : ℝ} (hxy : |x| ≤ |y|) :
    spinWc a x ≤ spinWc a y := by
  rw [← spinWc_abs a x, ← spinWc_abs a y]
  have h := spinWc_exp_mono ha (abs_nonneg x) hxy
  have hexp : Real.exp (-(4 * π * a * (|y| - |x|))) ≤ 1 := by
    refine Real.exp_le_one_iff.mpr ?_
    have : 0 ≤ 4 * π * a * (|y| - |x|) := by
      have ha0 : 0 ≤ a := by linarith
      have hsub : 0 ≤ |y| - |x| := sub_nonneg.mpr hxy
      positivity
    linarith
  calc spinWc a |x|
      ≤ Real.exp (-(4 * π * a * (|y| - |x|))) * spinWc a |y| := h
    _ ≤ 1 * spinWc a |y| := mul_le_mul_of_nonneg_right hexp (spinWc_nonneg ha |y|)
    _ = spinWc a |y| := one_mul _

private lemma continuous_spinWc (a : ℝ) : Continuous (spinWc a) := by
  unfold spinWc spinV1; fun_prop

private lemma integrable_comp_prod_scale {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    {f : ℝ × ℝ → ℝ} (hf : Integrable f volume) :
    Integrable (fun p : ℝ × ℝ => f (c₁ * p.1, c₂ * p.2)) volume := by
  let e : ℝ × ℝ ≃ᵐ ℝ × ℝ :=
    (MeasurableEquiv.mulLeft₀ c₁ hc₁.ne').prodCongr (MeasurableEquiv.mulLeft₀ c₂ hc₂.ne')
  have hmp : Measure.map e (volume : Measure (ℝ × ℝ)) =
      ENNReal.ofReal (c₁⁻¹ * c₂⁻¹) • (volume : Measure (ℝ × ℝ)) := by
    have he : (e : ℝ × ℝ → ℝ × ℝ) = Prod.map (c₁ * ·) (c₂ * ·) := rfl
    rw [he, Measure.volume_eq_prod,
      ← Measure.map_prod_map _ _ (measurable_const_mul c₁) (measurable_const_mul c₂),
      Real.map_volume_mul_left hc₁.ne', Real.map_volume_mul_left hc₂.ne',
      Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
      abs_of_pos (inv_pos.mpr hc₁), abs_of_pos (inv_pos.mpr hc₂),
      ENNReal.ofReal_mul (inv_pos.mpr hc₁).le]
  have hf_map : Integrable f (Measure.map e volume) := by
    rw [hmp]
    exact hf.smul_measure ENNReal.ofReal_ne_top
  exact (MeasurePreserving.integrable_comp_emb ⟨e.measurable, rfl⟩ e.measurableEmbedding).mpr hf_map

lemma integrable_spinG_wc {a : ℝ} (ha : 0 < a) {Φ : ℝ × ℝ → ℝ} (hΦ : SpinTestClass a Φ) :
    Integrable (fun p : ℝ × ℝ => |spinG a Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2) volume := by
  let c : ℝ := 2 * Real.sqrt a
  have hc : 0 < c := by positivity
  have h1 := integrable_comp_prod_scale hc hc hΦ.int_M2
  have h2 : Integrable (fun p : ℝ × ℝ =>
      (c * c) * (|Φ (c * p.1, c * p.2)| * spinV1 a (c * p.1) * spinV1 a (c * p.2))) volume :=
    h1.const_mul (c * c)
  refine h2.congr (Eventually.of_forall fun p => ?_)
  unfold spinG spinWc
  dsimp [c]
  ring

private lemma integrable_and_integral_spinG_dilate_wc {a : ℝ} (ha : 2 ≤ a)
    {Φ : ℝ × ℝ → ℝ} (hΦ : SpinTestClass a Φ) {c₁ c₂ : ℝ} (hc₁ : 1 ≤ c₁) (hc₂ : 1 ≤ c₂) :
    Integrable (fun p : ℝ × ℝ =>
        |spinG a Φ (c₁ * p.1) (c₂ * p.2)| * spinWc a p.1 * spinWc a p.2) volume ∧
      (∫ p : ℝ × ℝ, |spinG a Φ (c₁ * p.1) (c₂ * p.2)| * spinWc a p.1 * spinWc a p.2) ≤
        (c₁ * c₂)⁻¹ * spinM2 a Φ := by
  have ha0 : 0 < a := by linarith
  have hc₁_pos : 0 < c₁ := by linarith
  have hc₂_pos : 0 < c₂ := by linarith
  have hbase := integrable_spinG_wc ha0 hΦ
  have hdom := integrable_comp_prod_scale hc₁_pos hc₂_pos hbase
  have hmeas : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      |spinG a Φ (c₁ * p.1) (c₂ * p.2)| * spinWc a p.1 * spinWc a p.2) volume := by
    have hG : Continuous (fun p : ℝ × ℝ => spinG a Φ (c₁ * p.1) (c₂ * p.2)) := by
      unfold spinG
      exact hΦ.cont.comp ((continuous_const.mul (continuous_const.mul continuous_fst)).prodMk
        (continuous_const.mul (continuous_const.mul continuous_snd)))
    exact ((hG.abs.mul ((continuous_spinWc a).comp continuous_fst)).mul
      ((continuous_spinWc a).comp continuous_snd)).aestronglyMeasurable
  have hpt : ∀ p : ℝ × ℝ,
      |spinG a Φ (c₁ * p.1) (c₂ * p.2)| * spinWc a p.1 * spinWc a p.2 ≤
        |spinG a Φ (c₁ * p.1) (c₂ * p.2)| * spinWc a (c₁ * p.1) * spinWc a (c₂ * p.2) := by
    intro p
    have hw1 : spinWc a p.1 ≤ spinWc a (c₁ * p.1) := by
      refine spinWc_mono_abs ha ?_
      rw [abs_mul, abs_of_pos hc₁_pos]
      nlinarith [abs_nonneg p.1]
    have hw2 : spinWc a p.2 ≤ spinWc a (c₂ * p.2) := by
      refine spinWc_mono_abs ha ?_
      rw [abs_mul, abs_of_pos hc₂_pos]
      nlinarith [abs_nonneg p.2]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hw1 (abs_nonneg _)) hw2
      (spinWc_nonneg ha p.2) (mul_nonneg (abs_nonneg _) (spinWc_nonneg ha (c₁ * p.1)))
  have hint : Integrable (fun p : ℝ × ℝ =>
      |spinG a Φ (c₁ * p.1) (c₂ * p.2)| * spinWc a p.1 * spinWc a p.2) volume := by
    refine hdom.mono' hmeas (Eventually.of_forall fun p => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) (spinWc_nonneg ha p.1))
      (spinWc_nonneg ha p.2))]
    exact hpt p
  refine ⟨hint, ?_⟩
  have hscale := integral_prod_scale hc₁_pos hc₂_pos
    (fun p : ℝ × ℝ => |spinG a Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2)
  have heval : ∫ p : ℝ × ℝ,
      |spinG a Φ (c₁ * p.1) (c₂ * p.2)| * spinWc a (c₁ * p.1) * spinWc a (c₂ * p.2) =
      (c₁ * c₂)⁻¹ * spinM2 a Φ := by
    rw [spinM2_eq_spinWc ha0 Φ, hscale]
    have hne : c₁ * c₂ ≠ 0 := (mul_pos hc₁_pos hc₂_pos).ne'
    field_simp [hne]
  calc ∫ p : ℝ × ℝ, |spinG a Φ (c₁ * p.1) (c₂ * p.2)| * spinWc a p.1 * spinWc a p.2
      ≤ ∫ p : ℝ × ℝ, |spinG a Φ (c₁ * p.1) (c₂ * p.2)| * spinWc a (c₁ * p.1) *
          spinWc a (c₂ * p.2) := integral_mono hint hdom hpt
    _ = (c₁ * c₂)⁻¹ * spinM2 a Φ := heval

/-- Outward `L¹` integrability and bound (`spinning_foundations.tex`, Lemma S2.2):
for `a > 2` and `Φ ∈ \overline{\mathcal A}_{\rm spin}`,
`∬ |Δ_a G| w_c ⊗ w_c ≤ (1 + λ⁻¹)² M_2[Φ]`. -/
theorem integrable_and_integral_spinDeltaA_wc {a : ℝ} (ha : 2 < a)
    {Φ : ℝ × ℝ → ℝ} (hΦ : SpinTestClass a Φ) :
    Integrable (fun p : ℝ × ℝ => |spinDeltaA a Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2) volume ∧
      (∫ p : ℝ × ℝ, |spinDeltaA a Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2) ≤
        (1 + (spinLambda a)⁻¹) ^ 2 * spinM2 a Φ := by
  have ha2 : 2 ≤ a := ha.le
  have hlam : 1 ≤ spinLambda a := spinLambda_ge_one' ha
  have h00 := integrable_and_integral_spinG_dilate_wc ha2 hΦ le_rfl le_rfl
  have h10 := integrable_and_integral_spinG_dilate_wc ha2 hΦ hlam le_rfl
  have h01 := integrable_and_integral_spinG_dilate_wc ha2 hΦ le_rfl hlam
  have h11 := integrable_and_integral_spinG_dilate_wc ha2 hΦ hlam hlam
  let f00 : ℝ × ℝ → ℝ := fun p => |spinG a Φ (1 * p.1) (1 * p.2)| * spinWc a p.1 * spinWc a p.2
  let f10 : ℝ × ℝ → ℝ := fun p =>
    |spinG a Φ (spinLambda a * p.1) (1 * p.2)| * spinWc a p.1 * spinWc a p.2
  let f01 : ℝ × ℝ → ℝ := fun p =>
    |spinG a Φ (1 * p.1) (spinLambda a * p.2)| * spinWc a p.1 * spinWc a p.2
  let f11 : ℝ × ℝ → ℝ := fun p =>
    |spinG a Φ (spinLambda a * p.1) (spinLambda a * p.2)| * spinWc a p.1 * spinWc a p.2
  have hsum_int : Integrable (fun p : ℝ × ℝ => f00 p + f10 p + f01 p + f11 p) volume :=
    ((h00.1.add h10.1).add h01.1).add h11.1
  have hpt : ∀ p : ℝ × ℝ,
      |spinDeltaA a Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2 ≤
        f00 p + f10 p + f01 p + f11 p := by
    intro p
    have htri : |spinDeltaA a Φ p.1 p.2| ≤
        |spinG a Φ (1 * p.1) (1 * p.2)| + |spinG a Φ (spinLambda a * p.1) (1 * p.2)| +
        |spinG a Φ (1 * p.1) (spinLambda a * p.2)| +
        |spinG a Φ (spinLambda a * p.1) (spinLambda a * p.2)| := by
      rw [spinDeltaA_expand ha]
      simp only [one_mul]
      have h1 := abs_add_le
        (spinG a Φ (spinLambda a * p.1) (spinLambda a * p.2) -
          spinG a Φ p.1 (spinLambda a * p.2) - spinG a Φ (spinLambda a * p.1) p.2)
        (spinG a Φ p.1 p.2)
      have h2 := abs_sub
        (spinG a Φ (spinLambda a * p.1) (spinLambda a * p.2) -
          spinG a Φ p.1 (spinLambda a * p.2))
        (spinG a Φ (spinLambda a * p.1) p.2)
      have h3 := abs_sub
        (spinG a Φ (spinLambda a * p.1) (spinLambda a * p.2))
        (spinG a Φ p.1 (spinLambda a * p.2))
      linarith
    have hw : 0 ≤ spinWc a p.1 * spinWc a p.2 :=
      mul_nonneg (spinWc_nonneg ha2 p.1) (spinWc_nonneg ha2 p.2)
    have hmul := mul_le_mul_of_nonneg_right htri hw
    dsimp [f00, f10, f01, f11]
    linarith
  have hmeas : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      |spinDeltaA a Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2) volume := by
    have hG_cont : ∀ c₁ c₂ : ℝ, Continuous (fun p : ℝ × ℝ => spinG a Φ (c₁ * p.1) (c₂ * p.2)) := by
      intro c₁ c₂; unfold spinG
      exact hΦ.cont.comp ((continuous_const.mul (continuous_const.mul continuous_fst)).prodMk
        (continuous_const.mul (continuous_const.mul continuous_snd)))
    have hD_cont : Continuous (fun p : ℝ × ℝ => spinDeltaA a Φ p.1 p.2) := by
      have heq : (fun p : ℝ × ℝ => spinDeltaA a Φ p.1 p.2) =
          fun p => spinG a Φ (spinLambda a * p.1) (spinLambda a * p.2) -
            spinG a Φ (1 * p.1) (spinLambda a * p.2) -
            spinG a Φ (spinLambda a * p.1) (1 * p.2) +
            spinG a Φ (1 * p.1) (1 * p.2) := by
        ext p; rw [spinDeltaA_expand ha]; simp only [one_mul]
      rw [heq]
      exact (((hG_cont (spinLambda a) (spinLambda a)).sub (hG_cont 1 (spinLambda a))).sub
        (hG_cont (spinLambda a) 1)).add (hG_cont 1 1)
    exact ((hD_cont.abs.mul ((continuous_spinWc a).comp continuous_fst)).mul
      ((continuous_spinWc a).comp continuous_snd)).aestronglyMeasurable
  have hint : Integrable (fun p : ℝ × ℝ =>
      |spinDeltaA a Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2) volume := by
    refine hsum_int.mono' hmeas (Eventually.of_forall fun p => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) (spinWc_nonneg ha2 p.1))
      (spinWc_nonneg ha2 p.2))]
    exact hpt p
  refine ⟨hint, ?_⟩
  have h12 : Integrable (fun p : ℝ × ℝ => f00 p + f10 p) volume := h00.1.add h10.1
  have h123 : Integrable (fun p : ℝ × ℝ => f00 p + f10 p + f01 p) volume := h12.add h01.1
  have hsum_eq : ∫ p : ℝ × ℝ, (f00 p + f10 p + f01 p + f11 p) =
      (∫ p, f00 p) + (∫ p, f10 p) + (∫ p, f01 p) + (∫ p, f11 p) := by
    rw [integral_add h123 h11.1, integral_add h12 h01.1, integral_add h00.1 h10.1]
  have halg :
      (1 * 1)⁻¹ * spinM2 a Φ + (spinLambda a * 1)⁻¹ * spinM2 a Φ +
        (1 * spinLambda a)⁻¹ * spinM2 a Φ + (spinLambda a * spinLambda a)⁻¹ * spinM2 a Φ =
      (1 + (spinLambda a)⁻¹) ^ 2 * spinM2 a Φ := by
    rw [mul_inv]
    ring
  calc ∫ p : ℝ × ℝ, |spinDeltaA a Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2
      ≤ ∫ p : ℝ × ℝ, (f00 p + f10 p + f01 p + f11 p) := integral_mono hint hsum_int hpt
    _ = (∫ p, f00 p) + (∫ p, f10 p) + (∫ p, f01 p) + (∫ p, f11 p) := hsum_eq
    _ ≤ (1 * 1)⁻¹ * spinM2 a Φ + (spinLambda a * 1)⁻¹ * spinM2 a Φ +
          (1 * spinLambda a)⁻¹ * spinM2 a Φ + (spinLambda a * spinLambda a)⁻¹ * spinM2 a Φ := by
        linarith [h00.2, h10.2, h01.2, h11.2]
    _ = (1 + (spinLambda a)⁻¹) ^ 2 * spinM2 a Φ := halg

/-! ### Part 2: Inward `L¹(w_c ⊗ w_c)` unboundedness via Gaussian family `Φ_s` -/

/-- The `D_4`-invariant Fourier-odd Gaussian test family
`Φ_s(r_L, r_R) = e^{-π s (r_L² + r_R²)} - s⁻¹ e^{-π (r_L² + r_R²) / s}` (`s > 0`). -/
noncomputable def spinGaussTest (s : ℝ) (p : ℝ × ℝ) : ℝ :=
  Real.exp (-π * s * (p.1 ^ 2 + p.2 ^ 2)) - s⁻¹ * Real.exp (-π * (p.1 ^ 2 + p.2 ^ 2) / s)

private lemma integrable_exp_neg_mul_sq_add_linear {p : ℝ} (hp : 0 < p) (α : ℝ) :
    Integrable (fun x : ℝ => Real.exp (-p * x ^ 2 + α * x)) volume := by
  have h1 : Integrable (fun x : ℝ => Real.exp (-p * (x - α / (2 * p)) ^ 2)) volume :=
    (integrable_exp_neg_mul_sq hp).comp_sub_right (α / (2 * p))
  have h2 := h1.const_mul (Real.exp (α ^ 2 / (4 * p)))
  refine h2.congr (Eventually.of_forall fun x => ?_)
  dsimp only
  rw [← Real.exp_add]
  congr 1
  field_simp [hp.ne']
  ring

private lemma integral_exp_neg_mul_sq_add_linear {p : ℝ} (hp : 0 < p) (α : ℝ) :
    ∫ x : ℝ, Real.exp (-p * x ^ 2 + α * x) = Real.sqrt (π / p) * Real.exp (α ^ 2 / (4 * p)) := by
  have heq : (fun x : ℝ => Real.exp (-p * x ^ 2 + α * x)) =
      fun x => Real.exp (α ^ 2 / (4 * p)) * Real.exp (-p * (x - α / (2 * p)) ^ 2) := by
    ext x
    rw [← Real.exp_add]
    congr 1
    field_simp [hp.ne']
    ring
  rw [heq, integral_const_mul,
    MeasureTheory.integral_sub_right_eq_self (fun x => Real.exp (-p * x ^ 2)) (α / (2 * p)),
    integral_gaussian p, mul_comm]

private lemma integrable_exp_neg_mul_sq_mul_cosh {p : ℝ} (hp : 0 < p) (α : ℝ) :
    Integrable (fun x : ℝ => Real.exp (-p * x ^ 2) * Real.cosh (α * x)) volume := by
  have h1 := integrable_exp_neg_mul_sq_add_linear hp α
  have h2 := integrable_exp_neg_mul_sq_add_linear hp (-α)
  refine ((h1.add h2).const_mul (1 / 2 : ℝ)).congr (Eventually.of_forall fun x => ?_)
  simp only [Pi.add_apply]
  rw [Real.cosh_eq, ← mul_div_assoc, Real.exp_add, Real.exp_add]
  have hneg : -α * x = -(α * x) := by ring
  rw [hneg]; ring

private lemma integral_exp_neg_mul_sq_mul_cosh {p : ℝ} (hp : 0 < p) (α : ℝ) :
    ∫ x : ℝ, Real.exp (-p * x ^ 2) * Real.cosh (α * x) =
      Real.sqrt (π / p) * Real.exp (α ^ 2 / (4 * p)) := by
  have h1 := integrable_exp_neg_mul_sq_add_linear hp α
  have h2 := integrable_exp_neg_mul_sq_add_linear hp (-α)
  have heq : (fun x : ℝ => Real.exp (-p * x ^ 2) * Real.cosh (α * x)) =
      fun x => (1 / 2 : ℝ) * (Real.exp (-p * x ^ 2 + α * x) + Real.exp (-p * x ^ 2 + (-α) * x)) := by
    ext x
    rw [Real.cosh_eq, ← mul_div_assoc, mul_add, ← Real.exp_add, ← Real.exp_add]
    have hneg : -p * x ^ 2 + -(α * x) = -p * x ^ 2 + -α * x := by ring
    rw [hneg]; ring
  rw [heq, integral_const_mul, integral_add h1 h2,
    integral_exp_neg_mul_sq_add_linear hp α, integral_exp_neg_mul_sq_add_linear hp (-α), neg_sq]
  ring

/-- 1D Gaussian weighted integral `J_a(p) = ∫_ℝ e^{-p x²} w_c(x) dx`. -/
private noncomputable def spinGaussJ (a p : ℝ) : ℝ :=
  ∫ x : ℝ, Real.exp (-p * x ^ 2) * spinWc a x

private lemma sqrt_mul_spinGamma {a : ℝ} (ha : 2 ≤ a) :
    Real.sqrt a * spinGamma a = Real.sqrt (a - 2) := by
  unfold spinGamma
  rw [← Real.sqrt_mul (by linarith)]
  congr 1; field_simp [(by linarith : a ≠ 0)]

private lemma integrable_exp_neg_mul_sq_mul_spinWc {a p : ℝ} (ha : 2 ≤ a) (hp : 0 < p) :
    Integrable (fun x : ℝ => Real.exp (-p * x ^ 2) * spinWc a x) volume := by
  have ha0 : 0 ≤ a := by linarith
  have h1 := integrable_exp_neg_mul_sq_mul_cosh hp (4 * π * a)
  have h2 := integrable_exp_neg_mul_sq_mul_cosh hp (4 * π * a * spinGamma a)
  refine ((h1.sub h2).const_mul (2 * Real.sqrt a)).congr (Eventually.of_forall fun x => ?_)
  simp only [Pi.sub_apply]
  unfold spinWc spinV1
  have hmul1 : 2 * π * Real.sqrt a * (2 * Real.sqrt a * x) = 4 * π * a * x := by
    have : Real.sqrt a * Real.sqrt a = a := Real.mul_self_sqrt ha0
    calc 2 * π * Real.sqrt a * (2 * Real.sqrt a * x)
        = 4 * π * (Real.sqrt a * Real.sqrt a) * x := by ring
      _ = 4 * π * a * x := by rw [this]
  have hmul2 : 2 * π * Real.sqrt (a - 2) * (2 * Real.sqrt a * x) =
      4 * π * a * spinGamma a * x := by
    have hg := sqrt_mul_spinGamma ha
    have hsq : Real.sqrt a * Real.sqrt a = a := Real.mul_self_sqrt ha0
    calc 2 * π * Real.sqrt (a - 2) * (2 * Real.sqrt a * x)
        = 4 * π * (Real.sqrt a * (Real.sqrt a * spinGamma a)) * x := by rw [hg]; ring
      _ = 4 * π * ((Real.sqrt a * Real.sqrt a) * spinGamma a) * x := by ring
      _ = 4 * π * (a * spinGamma a) * x := by rw [hsq]
      _ = 4 * π * a * spinGamma a * x := by ring
  rw [hmul1, hmul2]; ring

private lemma spinGaussJ_eq {a p : ℝ} (ha : 2 ≤ a) (hp : 0 < p) :
    spinGaussJ a p = 2 * Real.sqrt (a * π / p) *
      (Real.exp ((4 * π * a) ^ 2 / (4 * p)) -
        Real.exp ((4 * π * a * spinGamma a) ^ 2 / (4 * p))) := by
  have ha0 : 0 ≤ a := by linarith
  have h1 := integrable_exp_neg_mul_sq_mul_cosh hp (4 * π * a)
  have h2 := integrable_exp_neg_mul_sq_mul_cosh hp (4 * π * a * spinGamma a)
  have heq : (fun x : ℝ => Real.exp (-p * x ^ 2) * spinWc a x) =
      fun x => (2 * Real.sqrt a) *
        (Real.exp (-p * x ^ 2) * Real.cosh (4 * π * a * x) -
         Real.exp (-p * x ^ 2) * Real.cosh (4 * π * a * spinGamma a * x)) := by
    ext x
    unfold spinWc spinV1
    have hmul1 : 2 * π * Real.sqrt a * (2 * Real.sqrt a * x) = 4 * π * a * x := by
      have : Real.sqrt a * Real.sqrt a = a := Real.mul_self_sqrt ha0
      calc 2 * π * Real.sqrt a * (2 * Real.sqrt a * x)
          = 4 * π * (Real.sqrt a * Real.sqrt a) * x := by ring
        _ = 4 * π * a * x := by rw [this]
    have hmul2 : 2 * π * Real.sqrt (a - 2) * (2 * Real.sqrt a * x) =
        4 * π * a * spinGamma a * x := by
      have hg := sqrt_mul_spinGamma ha
      have hsq : Real.sqrt a * Real.sqrt a = a := Real.mul_self_sqrt ha0
      calc 2 * π * Real.sqrt (a - 2) * (2 * Real.sqrt a * x)
          = 4 * π * (Real.sqrt a * (Real.sqrt a * spinGamma a)) * x := by rw [hg]; ring
        _ = 4 * π * ((Real.sqrt a * Real.sqrt a) * spinGamma a) * x := by ring
        _ = 4 * π * (a * spinGamma a) * x := by rw [hsq]
        _ = 4 * π * a * spinGamma a * x := by ring
    rw [hmul1, hmul2]; ring
  unfold spinGaussJ
  rw [heq, integral_const_mul, integral_sub h1 h2,
    integral_exp_neg_mul_sq_mul_cosh hp (4 * π * a),
    integral_exp_neg_mul_sq_mul_cosh hp (4 * π * a * spinGamma a)]
  have hsqrt : Real.sqrt a * Real.sqrt (π / p) = Real.sqrt (a * π / p) := by
    rw [← Real.sqrt_mul ha0, mul_div_assoc]
  calc 2 * Real.sqrt a * (Real.sqrt (π / p) * Real.exp ((4 * π * a) ^ 2 / (4 * p)) -
          Real.sqrt (π / p) * Real.exp ((4 * π * a * spinGamma a) ^ 2 / (4 * p)))
      = 2 * (Real.sqrt a * Real.sqrt (π / p)) *
          (Real.exp ((4 * π * a) ^ 2 / (4 * p)) -
            Real.exp ((4 * π * a * spinGamma a) ^ 2 / (4 * p))) := by ring
    _ = 2 * Real.sqrt (a * π / p) *
          (Real.exp ((4 * π * a) ^ 2 / (4 * p)) -
            Real.exp ((4 * π * a * spinGamma a) ^ 2 / (4 * p))) := by rw [hsqrt]

private lemma fourier_spinGauss_single {r : ℝ} (hr : 0 < r) :
    𝓕 (fun v : EuclideanSpace ℝ (Fin 2) =>
        (Real.exp (-π * r * (v 0 ^ 2 + v 1 ^ 2)) : ℂ)) =
      fun ξ : EuclideanSpace ℝ (Fin 2) =>
        (r⁻¹ : ℂ) * (Real.exp (-π * (ξ 0 ^ 2 + ξ 1 ^ 2) / r) : ℂ) := by
  have hb : 0 < ((π * r : ℝ) : ℂ).re := by simp [Real.pi_pos, hr]
  have hfn : (fun v : EuclideanSpace ℝ (Fin 2) =>
        (Real.exp (-π * r * (v 0 ^ 2 + v 1 ^ 2)) : ℂ)) =
      fun v : EuclideanSpace ℝ (Fin 2) =>
        Complex.exp (-((π * r : ℝ) : ℂ) * (‖v‖ : ℂ) ^ 2) := by
    ext v
    rw [Complex.ofReal_exp]
    congr 1
    have hnorm : ‖v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
      simp [Real.norm_eq_abs, sq_abs]
    rw [show (‖v‖ : ℂ) ^ 2 = ((‖v‖ ^ 2 : ℝ) : ℂ) by push_cast; rfl, hnorm]
    push_cast; ring
  rw [hfn]
  ext ξ
  rw [fourier_gaussian_innerProductSpace hb ξ]
  have hdim : (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) / 2 : ℂ) = 1 := by
    rw [finrank_euclideanSpace_fin]; norm_num
  rw [hdim, Complex.cpow_one]
  have hpi : ((π : ℝ) : ℂ) / ((π * r : ℝ) : ℂ) = (r⁻¹ : ℂ) := by
    have hp : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
    have hrc : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
    push_cast; field_simp
  rw [hpi, Complex.ofReal_exp]
  congr 2
  have hnorm : ‖ξ‖ ^ 2 = ξ 0 ^ 2 + ξ 1 ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
    simp [Real.norm_eq_abs, sq_abs]
  rw [show (‖ξ‖ : ℂ) ^ 2 = ((‖ξ‖ ^ 2 : ℝ) : ℂ) by push_cast; rfl, hnorm]
  have hp : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  have hrc : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  push_cast; field_simp

private lemma integrable_spinGauss_euc {r : ℝ} (hr : 0 < r) :
    Integrable (fun v : EuclideanSpace ℝ (Fin 2) =>
      (Real.exp (-π * r * (v 0 ^ 2 + v 1 ^ 2)) : ℂ)) volume := by
  have hb : 0 < ((π * r : ℝ) : ℂ).re := by simp [Real.pi_pos, hr]
  have hfn : (fun v : EuclideanSpace ℝ (Fin 2) =>
        (Real.exp (-π * r * (v 0 ^ 2 + v 1 ^ 2)) : ℂ)) =
      fun v : EuclideanSpace ℝ (Fin 2) =>
        Complex.exp (-((π * r : ℝ) : ℂ) * (‖v‖ : ℂ) ^ 2) := by
    ext v
    rw [Complex.ofReal_exp]
    congr 1
    have hnorm : ‖v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
      simp [Real.norm_eq_abs, sq_abs]
    rw [show (‖v‖ : ℂ) ^ 2 = ((‖v‖ ^ 2 : ℝ) : ℂ) by push_cast; rfl, hnorm]
    push_cast; ring
  rw [hfn]
  simpa using GaussianFourier.integrable_cexp_neg_mul_sq_norm_add hb 0
    (0 : EuclideanSpace ℝ (Fin 2))

private lemma integrable_exp_neg_mul_sq_prod {r : ℝ} (hr : 0 < r) :
    Integrable (fun p : ℝ × ℝ => Real.exp (-π * r * (p.1 ^ 2 + p.2 ^ 2))) volume := by
  have h1 : Integrable (fun x : ℝ => Real.exp (-(π * r) * x ^ 2)) volume :=
    integrable_exp_neg_mul_sq (by positivity)
  have hprod : Integrable (fun p : ℝ × ℝ =>
      Real.exp (-(π * r) * p.1 ^ 2) * Real.exp (-(π * r) * p.2 ^ 2)) volume :=
    h1.mul_prod h1
  refine hprod.congr (Eventually.of_forall fun p => ?_)
  dsimp only
  rw [← Real.exp_add]; congr 1; ring

private lemma integrable_exp_neg_mul_sq_mul_spinV1 {a r : ℝ} (_ha : 2 ≤ a) (hr : 0 < r) :
    Integrable (fun x : ℝ => Real.exp (-π * r * x ^ 2) * spinV1 a x) volume := by
  have h1 := integrable_exp_neg_mul_sq_mul_cosh (by positivity : 0 < π * r) (2 * π * Real.sqrt a)
  have h2 := integrable_exp_neg_mul_sq_mul_cosh (by positivity : 0 < π * r) (2 * π * Real.sqrt (a - 2))
  refine (h1.sub h2).congr (Eventually.of_forall fun x => ?_)
  simp only [Pi.sub_apply]
  unfold spinV1
  have hmul : -(π * r) * x ^ 2 = -π * r * x ^ 2 := by ring
  rw [hmul]; ring

private lemma integrable_fourier_mul_euc {f : EuclideanSpace ℝ (Fin 2) → ℂ}
    (hf : Integrable f volume) (ξ : EuclideanSpace ℝ (Fin 2)) :
    Integrable (fun v : EuclideanSpace ℝ (Fin 2) => 𝐞 (-⟪v, ξ⟫_ℝ) • f v) volume := by
  have hcont : Continuous (fun v : EuclideanSpace ℝ (Fin 2) =>
      Complex.exp (2 * π * I * ((-⟪v, ξ⟫_ℝ : ℝ) : ℂ))) := by fun_prop
  have hmeas : AEStronglyMeasurable (fun v : EuclideanSpace ℝ (Fin 2) => 𝐞 (-⟪v, ξ⟫_ℝ) • f v) volume := by
    refine (hcont.aestronglyMeasurable.mul hf.aestronglyMeasurable).congr (Eventually.of_forall fun v => ?_)
    simp only [Pi.mul_apply, Circle.smul_def, smul_eq_mul, Real.fourierChar_apply]
    congr 2; push_cast; ring
  refine hf.norm.mono' hmeas (Eventually.of_forall fun v => ?_)
  rw [Circle.smul_def, smul_eq_mul, norm_mul, Circle.norm_coe, one_mul]

private lemma fourier_sub_euc {f g : EuclideanSpace ℝ (Fin 2) → ℂ}
    (hf : Integrable f volume) (hg : Integrable g volume) :
    𝓕 (f - g) = 𝓕 f - 𝓕 g := by
  ext ξ
  simp only [Pi.sub_apply, Real.fourier_eq]
  rw [← integral_sub (integrable_fourier_mul_euc hf ξ) (integrable_fourier_mul_euc hg ξ)]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp [smul_sub]

private lemma fourier_const_smul_euc (c : ℂ) (f : EuclideanSpace ℝ (Fin 2) → ℂ) :
    𝓕 (c • f) = c • 𝓕 f := by
  ext ξ
  simp only [Pi.smul_apply, Real.fourier_eq]
  rw [← integral_smul]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp [Circle.smul_def, smul_eq_mul]; ring

lemma spinGaussTest_mem_SpinTestClass {a : ℝ} (ha : 2 ≤ a) {s : ℝ} (hs : 0 < s) :
    SpinTestClass a (spinGaussTest s) where
  cont := by unfold spinGaussTest; fun_prop
  int := by
    unfold spinGaussTest
    have h1 := integrable_exp_neg_mul_sq_prod hs
    have h2 : Integrable (fun p : ℝ × ℝ =>
        s⁻¹ * Real.exp (-π * (p.1 ^ 2 + p.2 ^ 2) / s)) volume := by
      refine ((integrable_exp_neg_mul_sq_prod (inv_pos.mpr hs)).const_mul s⁻¹).congr
        (Eventually.of_forall fun p => ?_)
      dsimp only; congr 2; ring
    exact h1.sub h2
  d4_inv := by
    refine ⟨fun x y => ?_, fun x y => ?_, fun x y => ?_⟩ <;>
      · unfold spinGaussTest; ring_nf
  fourier_odd := by
    have hsplit : spinToEuc (spinGaussTest s) =
        (fun v : EuclideanSpace ℝ (Fin 2) => (Real.exp (-π * s * (v 0 ^ 2 + v 1 ^ 2)) : ℂ)) -
        ((s⁻¹ : ℝ) : ℂ) • (fun v : EuclideanSpace ℝ (Fin 2) =>
          (Real.exp (-π * s⁻¹ * (v 0 ^ 2 + v 1 ^ 2)) : ℂ)) := by
      ext v
      unfold spinToEuc spinGaussTest
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Complex.ofReal_sub, Complex.ofReal_mul]
      congr 2; ring_nf
    rw [hsplit]
    have h1 := integrable_spinGauss_euc hs
    have h2 := (integrable_spinGauss_euc (inv_pos.mpr hs)).smul ((s⁻¹ : ℝ) : ℂ)
    rw [fourier_sub_euc h1 h2, fourier_const_smul_euc,
      fourier_spinGauss_single hs, fourier_spinGauss_single (inv_pos.mpr hs)]
    ext ξ
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    have hs_ne : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
    have he1 : -π * (ξ 0 ^ 2 + ξ 1 ^ 2) / s = -π * s⁻¹ * (ξ 0 ^ 2 + ξ 1 ^ 2) := by ring
    have he2 : -π * (ξ 0 ^ 2 + ξ 1 ^ 2) / s⁻¹ = -π * s * (ξ 0 ^ 2 + ξ 1 ^ 2) := by
      rw [div_inv_eq_mul]; ring
    rw [he1, he2]
    push_cast
    field_simp [hs_ne]
    ring
  int_M2 := by
    have h1x := integrable_exp_neg_mul_sq_mul_spinV1 ha hs
    have h2x := integrable_exp_neg_mul_sq_mul_spinV1 ha (inv_pos.mpr hs)
    have hdom : Integrable (fun p : ℝ × ℝ =>
        (Real.exp (-π * s * p.1 ^ 2) * spinV1 a p.1) *
          (Real.exp (-π * s * p.2 ^ 2) * spinV1 a p.2) +
        s⁻¹ * ((Real.exp (-π * s⁻¹ * p.1 ^ 2) * spinV1 a p.1) *
          (Real.exp (-π * s⁻¹ * p.2 ^ 2) * spinV1 a p.2))) volume :=
      (h1x.mul_prod h1x).add ((h2x.mul_prod h2x).const_mul s⁻¹)
    refine hdom.mono' ?_ (Eventually.of_forall fun p => ?_)
    · have hV : Continuous (spinV1 a) := by unfold spinV1; fun_prop
      have hΦ : Continuous (spinGaussTest s) := by unfold spinGaussTest; fun_prop
      exact ((hΦ.abs.mul (hV.comp continuous_fst)).mul (hV.comp continuous_snd)).aestronglyMeasurable
    · rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) (spinV1_nonneg ha p.1))
        (spinV1_nonneg ha p.2))]
      have habs : |spinGaussTest s p| ≤
          Real.exp (-π * s * (p.1 ^ 2 + p.2 ^ 2)) +
            s⁻¹ * Real.exp (-π * s⁻¹ * (p.1 ^ 2 + p.2 ^ 2)) := by
        unfold spinGaussTest
        calc |Real.exp (-π * s * (p.1 ^ 2 + p.2 ^ 2)) -
                s⁻¹ * Real.exp (-π * (p.1 ^ 2 + p.2 ^ 2) / s)|
            ≤ |Real.exp (-π * s * (p.1 ^ 2 + p.2 ^ 2))| +
                |s⁻¹ * Real.exp (-π * (p.1 ^ 2 + p.2 ^ 2) / s)| := abs_sub _ _
          _ = Real.exp (-π * s * (p.1 ^ 2 + p.2 ^ 2)) +
                s⁻¹ * Real.exp (-π * s⁻¹ * (p.1 ^ 2 + p.2 ^ 2)) := by
              rw [abs_of_pos (Real.exp_pos _), abs_of_pos (by positivity)]
              congr 3; ring
      have he1 : Real.exp (-π * s * (p.1 ^ 2 + p.2 ^ 2)) =
          Real.exp (-π * s * p.1 ^ 2) * Real.exp (-π * s * p.2 ^ 2) := by
        rw [← Real.exp_add]; congr 1; ring
      have he2 : Real.exp (-π * s⁻¹ * (p.1 ^ 2 + p.2 ^ 2)) =
          Real.exp (-π * s⁻¹ * p.1 ^ 2) * Real.exp (-π * s⁻¹ * p.2 ^ 2) := by
        rw [← Real.exp_add]; congr 1; ring
      have hv1 := spinV1_nonneg ha p.1
      have hv2 := spinV1_nonneg ha p.2
      have hmul := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right habs hv1) hv2
      rw [he1, he2] at hmul
      linarith

private lemma spinV1_pos_of_pos {a : ℝ} (ha : 2 < a) {r : ℝ} (hr : 0 < r) : 0 < spinV1 a r := by
  unfold spinV1
  have hsq : Real.sqrt (a - 2) < Real.sqrt a := Real.sqrt_lt_sqrt (by linarith) (by linarith)
  have hlt : 2 * π * Real.sqrt (a - 2) * r < 2 * π * Real.sqrt a * r :=
    mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hsq (by positivity)) hr
  have hch : Real.cosh (2 * π * Real.sqrt (a - 2) * r) < Real.cosh (2 * π * Real.sqrt a * r) := by
    refine Real.cosh_lt_cosh.mpr ?_
    rw [abs_of_pos (mul_pos (mul_pos (by positivity) (Real.sqrt_pos.mpr (by linarith))) hr),
      abs_of_pos (mul_pos (mul_pos (by positivity) (Real.sqrt_pos.mpr (by linarith))) hr)]
    exact hlt
  linarith

private lemma spinV1_mono_nonneg {a x y : ℝ} (ha : 2 ≤ a) (hx : 0 ≤ x) (hxy : x ≤ y) :
    spinV1 a x ≤ spinV1 a y := by
  have ha0 : 0 < a := by linarith
  have hc : 0 < 2 * Real.sqrt a := by positivity
  have h1 : spinWc a (x / (2 * Real.sqrt a)) ≤ spinWc a (y / (2 * Real.sqrt a)) := by
    refine spinWc_mono_abs ha ?_
    rw [abs_of_nonneg (div_nonneg hx hc.le), abs_of_nonneg (div_nonneg (hx.trans hxy) hc.le)]
    exact div_le_div_of_nonneg_right hxy hc.le
  unfold spinWc at h1
  rw [mul_div_cancel₀ _ hc.ne', mul_div_cancel₀ _ hc.ne'] at h1
  exact le_of_mul_le_mul_left h1 hc

private lemma spinGaussTest_M2_pos {a : ℝ} (ha : 2 < a) {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    0 < spinM2 a (spinGaussTest s) := by
  have ha2 : 2 ≤ a := ha.le
  have hval0 : spinGaussTest s (0, 0) < 0 := by
    unfold spinGaussTest
    simp only [sq, mul_zero, add_zero, zero_div, Real.exp_zero, mul_one]
    have : 1 < s⁻¹ := (one_lt_inv₀ hs).mpr hs1
    linarith
  set m : ℝ := -(spinGaussTest s (0, 0)) / 2
  have hm_pos : 0 < m := by dsimp [m]; linarith
  have hcont : Continuous (spinGaussTest s) := (spinGaussTest_mem_SpinTestClass ha2 hs).cont
  have hnhds : {p : ℝ × ℝ | spinGaussTest s p < -m} ∈ 𝓝 ((0 : ℝ), (0 : ℝ)) :=
    (isOpen_lt hcont continuous_const).mem_nhds (by dsimp [m]; linarith)
  rw [Metric.mem_nhds_iff] at hnhds
  obtain ⟨δ, hδ_pos, hδ_sub⟩ := hnhds
  set B : Set (ℝ × ℝ) := Icc (δ / 4) (δ / 2) ×ˢ Icc (δ / 4) (δ / 2)
  have hB_meas : MeasurableSet B := measurableSet_Icc.prod measurableSet_Icc
  set v0 : ℝ := spinV1 a (δ / 4)
  have hv0_pos : 0 < v0 := spinV1_pos_of_pos ha (by linarith)
  set c0 : ℝ := m * v0 * v0
  have hc0_pos : 0 < c0 := by positivity
  have hB_vol : volume.real B = (δ / 4) ^ 2 := by
    rw [Measure.real, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith)]
    ring
  have hB_fin : volume B ≠ ⊤ := by
    rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hpt : ∀ p ∈ B, c0 ≤ |spinGaussTest s p| * spinV1 a p.1 * spinV1 a p.2 := by
    intro p hp
    have hp1 : δ / 4 ≤ p.1 := hp.1.1
    have hp2 : δ / 4 ≤ p.2 := hp.2.1
    have hdist : dist p (0, 0) < δ := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_zero, sub_zero,
        abs_of_pos (by linarith), abs_of_pos (by linarith)]
      exact max_lt (by linarith [hp.1.2]) (by linarith [hp.2.2])
    have hlt : spinGaussTest s p < -m := hδ_sub hdist
    have habs : m ≤ |spinGaussTest s p| := by
      rw [abs_of_neg (by linarith)]; linarith
    have hv1 : v0 ≤ spinV1 a p.1 := spinV1_mono_nonneg ha2 (by linarith) hp1
    have hv2 : v0 ≤ spinV1 a p.2 := spinV1_mono_nonneg ha2 (by linarith) hp2
    exact mul_le_mul (mul_le_mul habs hv1 hv0_pos.le (abs_nonneg _)) hv2 hv0_pos.le
      (mul_nonneg (abs_nonneg _) (spinV1_nonneg ha2 p.1))
  have hint := (spinGaussTest_mem_SpinTestClass ha2 hs).int_M2
  have hle1 : (δ / 4) ^ 2 * c0 ≤
      ∫ p in B, |spinGaussTest s p| * spinV1 a p.1 * spinV1 a p.2 := by
    have hconst : ∫ _ in B, c0 = (δ / 4) ^ 2 * c0 := by
      rw [setIntegral_const, smul_eq_mul, hB_vol]
    rw [← hconst]
    exact setIntegral_mono_on (integrableOn_const hB_fin) hint.integrableOn hB_meas hpt
  have hle2 : ∫ p in B, |spinGaussTest s p| * spinV1 a p.1 * spinV1 a p.2 ≤
      spinM2 a (spinGaussTest s) :=
    setIntegral_le_integral hint (Eventually.of_forall fun p =>
      mul_nonneg (mul_nonneg (abs_nonneg _) (spinV1_nonneg ha2 p.1)) (spinV1_nonneg ha2 p.2))
  have hpos : 0 < (δ / 4) ^ 2 * c0 := by positivity
  linarith

private lemma spinGaussTest_M2_le {a : ℝ} (ha : 2 ≤ a) {s : ℝ} (hs : 0 < s) :
    spinM2 a (spinGaussTest s) ≤
      spinGaussJ a (4 * π * a * s) ^ 2 + s⁻¹ * spinGaussJ a (4 * π * a / s) ^ 2 := by
  have ha0 : 0 < a := by linarith
  set p := 4 * π * a * s
  set q := 4 * π * a / s
  have hp : 0 < p := by positivity
  have hq : 0 < q := by positivity
  have hIp := integrable_exp_neg_mul_sq_mul_spinWc ha hp
  have hIq := integrable_exp_neg_mul_sq_mul_spinWc ha hq
  have hdom : Integrable (fun z : ℝ × ℝ =>
      (Real.exp (-p * z.1 ^ 2) * spinWc a z.1) * (Real.exp (-p * z.2 ^ 2) * spinWc a z.2) +
      s⁻¹ * ((Real.exp (-q * z.1 ^ 2) * spinWc a z.1) *
        (Real.exp (-q * z.2 ^ 2) * spinWc a z.2))) volume :=
    (hIp.mul_prod hIp).add ((hIq.mul_prod hIq).const_mul s⁻¹)
  have hpt : ∀ z : ℝ × ℝ,
      |spinG a (spinGaussTest s) z.1 z.2| * spinWc a z.1 * spinWc a z.2 ≤
        (Real.exp (-p * z.1 ^ 2) * spinWc a z.1) * (Real.exp (-p * z.2 ^ 2) * spinWc a z.2) +
        s⁻¹ * ((Real.exp (-q * z.1 ^ 2) * spinWc a z.1) *
          (Real.exp (-q * z.2 ^ 2) * spinWc a z.2)) := by
    intro z
    have habs : |spinG a (spinGaussTest s) z.1 z.2| ≤
        Real.exp (-p * z.1 ^ 2) * Real.exp (-p * z.2 ^ 2) +
          s⁻¹ * (Real.exp (-q * z.1 ^ 2) * Real.exp (-q * z.2 ^ 2)) := by
      unfold spinG spinGaussTest
      have h1 : -π * s * ((2 * Real.sqrt a * z.1) ^ 2 + (2 * Real.sqrt a * z.2) ^ 2) =
          -p * z.1 ^ 2 + -p * z.2 ^ 2 := by
        have hsq : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha0.le
        dsimp [p]; ring_nf; rw [hsq]; ring
      have h2 : -π * ((2 * Real.sqrt a * z.1) ^ 2 + (2 * Real.sqrt a * z.2) ^ 2) / s =
          -q * z.1 ^ 2 + -q * z.2 ^ 2 := by
        have hsq : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha0.le
        dsimp [q]; field_simp [hs.ne']; ring_nf; rw [hsq]; ring
      rw [h1, h2, Real.exp_add, Real.exp_add]
      calc |Real.exp (-p * z.1 ^ 2) * Real.exp (-p * z.2 ^ 2) -
              s⁻¹ * (Real.exp (-q * z.1 ^ 2) * Real.exp (-q * z.2 ^ 2))|
          ≤ |Real.exp (-p * z.1 ^ 2) * Real.exp (-p * z.2 ^ 2)| +
              |s⁻¹ * (Real.exp (-q * z.1 ^ 2) * Real.exp (-q * z.2 ^ 2))| := abs_sub _ _
        _ = Real.exp (-p * z.1 ^ 2) * Real.exp (-p * z.2 ^ 2) +
              s⁻¹ * (Real.exp (-q * z.1 ^ 2) * Real.exp (-q * z.2 ^ 2)) := by
            rw [abs_of_pos (by positivity), abs_of_pos (by positivity)]
    have hw : 0 ≤ spinWc a z.1 * spinWc a z.2 :=
      mul_nonneg (spinWc_nonneg ha z.1) (spinWc_nonneg ha z.2)
    have hmul := mul_le_mul_of_nonneg_right habs hw
    linarith
  rw [spinM2_eq_spinWc ha0]
  calc ∫ z : ℝ × ℝ, |spinG a (spinGaussTest s) z.1 z.2| * spinWc a z.1 * spinWc a z.2
      ≤ ∫ z : ℝ × ℝ,
          ((Real.exp (-p * z.1 ^ 2) * spinWc a z.1) * (Real.exp (-p * z.2 ^ 2) * spinWc a z.2) +
          s⁻¹ * ((Real.exp (-q * z.1 ^ 2) * spinWc a z.1) *
            (Real.exp (-q * z.2 ^ 2) * spinWc a z.2))) :=
        integral_mono (integrable_spinG_wc ha0 (spinGaussTest_mem_SpinTestClass ha hs)) hdom hpt
    _ = (∫ z : ℝ × ℝ, (Real.exp (-p * z.1 ^ 2) * spinWc a z.1) *
          (Real.exp (-p * z.2 ^ 2) * spinWc a z.2)) +
        s⁻¹ * (∫ z : ℝ × ℝ, (Real.exp (-q * z.1 ^ 2) * spinWc a z.1) *
          (Real.exp (-q * z.2 ^ 2) * spinWc a z.2)) := by
        have h1 : Integrable (fun z : ℝ × ℝ =>
            (Real.exp (-p * z.1 ^ 2) * spinWc a z.1) * (Real.exp (-p * z.2 ^ 2) * spinWc a z.2))
            volume := hIp.mul_prod hIp
        have h2 : Integrable (fun z : ℝ × ℝ =>
            s⁻¹ * ((Real.exp (-q * z.1 ^ 2) * spinWc a z.1) *
              (Real.exp (-q * z.2 ^ 2) * spinWc a z.2))) volume :=
          (hIq.mul_prod hIq).const_mul s⁻¹
        rw [integral_add h1 h2, integral_const_mul]
    _ = spinGaussJ a p ^ 2 + s⁻¹ * spinGaussJ a q ^ 2 := by
        have hp_prod : ∫ z : ℝ × ℝ, (Real.exp (-p * z.1 ^ 2) * spinWc a z.1) *
            (Real.exp (-p * z.2 ^ 2) * spinWc a z.2) =
            (∫ x : ℝ, Real.exp (-p * x ^ 2) * spinWc a x) *
            (∫ y : ℝ, Real.exp (-p * y ^ 2) * spinWc a y) := by
          rw [Measure.volume_eq_prod]
          exact integral_prod_mul (fun x : ℝ => Real.exp (-p * x ^ 2) * spinWc a x)
            (fun y : ℝ => Real.exp (-p * y ^ 2) * spinWc a y)
        have hq_prod : ∫ z : ℝ × ℝ, (Real.exp (-q * z.1 ^ 2) * spinWc a z.1) *
            (Real.exp (-q * z.2 ^ 2) * spinWc a z.2) =
            (∫ x : ℝ, Real.exp (-q * x ^ 2) * spinWc a x) *
            (∫ y : ℝ, Real.exp (-q * y ^ 2) * spinWc a y) := by
          rw [Measure.volume_eq_prod]
          exact integral_prod_mul (fun x : ℝ => Real.exp (-q * x ^ 2) * spinWc a x)
            (fun y : ℝ => Real.exp (-q * y ^ 2) * spinWc a y)
        rw [hp_prod, hq_prod]; unfold spinGaussJ; ring

private lemma spinGaussTest_Da_ge {a : ℝ} (ha : 2 < a) {s : ℝ} (hs : 0 < s) :
    (spinGaussJ a (4 * π * a * s * spinGamma a ^ 2) - spinGaussJ a (4 * π * a * s)) ^ 2 -
      s⁻¹ * (spinGaussJ a (4 * π * a / s * spinGamma a ^ 2) -
        spinGaussJ a (4 * π * a / s)) ^ 2 ≤
      ∫ z : ℝ × ℝ, |spinDa a (spinGaussTest s) z.1 z.2| * spinWc a z.1 * spinWc a z.2 := by
  have ha2 : 2 ≤ a := ha.le
  have ha0 : 0 < a := by linarith
  have hγ_pos : 0 < spinGamma a := spinGamma_pos' ha
  set p := 4 * π * a * s
  set q := 4 * π * a / s
  have hp : 0 < p := by positivity
  have hq : 0 < q := by positivity
  have hpγ : 0 < p * spinGamma a ^ 2 := by positivity
  have hqγ : 0 < q * spinGamma a ^ 2 := by positivity
  let fp : ℝ → ℝ := fun x =>
    (Real.exp (-(p * spinGamma a ^ 2) * x ^ 2) - Real.exp (-p * x ^ 2)) * spinWc a x
  let fq : ℝ → ℝ := fun x =>
    (Real.exp (-(q * spinGamma a ^ 2) * x ^ 2) - Real.exp (-q * x ^ 2)) * spinWc a x
  have hfp_int : Integrable fp volume := by
    have h1 := integrable_exp_neg_mul_sq_mul_spinWc ha2 hpγ
    have h2 := integrable_exp_neg_mul_sq_mul_spinWc ha2 hp
    exact (h1.sub h2).congr (Eventually.of_forall fun x => by dsimp [fp]; ring)
  have hfq_int : Integrable fq volume := by
    have h1 := integrable_exp_neg_mul_sq_mul_spinWc ha2 hqγ
    have h2 := integrable_exp_neg_mul_sq_mul_spinWc ha2 hq
    exact (h1.sub h2).congr (Eventually.of_forall fun x => by dsimp [fq]; ring)
  have hfp_eval : ∫ x : ℝ, fp x = spinGaussJ a (p * spinGamma a ^ 2) - spinGaussJ a p := by
    have h1 := integrable_exp_neg_mul_sq_mul_spinWc ha2 hpγ
    have h2 := integrable_exp_neg_mul_sq_mul_spinWc ha2 hp
    have heq : fp = fun x =>
        Real.exp (-(p * spinGamma a ^ 2) * x ^ 2) * spinWc a x -
          Real.exp (-p * x ^ 2) * spinWc a x := by ext x; dsimp [fp]; ring
    rw [heq, integral_sub h1 h2]; rfl
  have hfq_eval : ∫ x : ℝ, fq x = spinGaussJ a (q * spinGamma a ^ 2) - spinGaussJ a q := by
    have h1 := integrable_exp_neg_mul_sq_mul_spinWc ha2 hqγ
    have h2 := integrable_exp_neg_mul_sq_mul_spinWc ha2 hq
    have heq : fq = fun x =>
        Real.exp (-(q * spinGamma a ^ 2) * x ^ 2) * spinWc a x -
          Real.exp (-q * x ^ 2) * spinWc a x := by ext x; dsimp [fq]; ring
    rw [heq, integral_sub h1 h2]; rfl
  have hDa_eq : ∀ z : ℝ × ℝ,
      spinDa a (spinGaussTest s) z.1 z.2 * spinWc a z.1 * spinWc a z.2 =
        fp z.1 * fp z.2 - s⁻¹ * (fq z.1 * fq z.2) := by
    intro z
    have hG_eq : ∀ u v : ℝ, spinG a (spinGaussTest s) u v =
        Real.exp (-p * u ^ 2) * Real.exp (-p * v ^ 2) -
          s⁻¹ * (Real.exp (-q * u ^ 2) * Real.exp (-q * v ^ 2)) := by
      intro u v
      unfold spinG spinGaussTest
      have h1 : -π * s * ((2 * Real.sqrt a * u) ^ 2 + (2 * Real.sqrt a * v) ^ 2) =
          -p * u ^ 2 + -p * v ^ 2 := by
        have hsq : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha0.le
        dsimp [p]; ring_nf; rw [hsq]; ring
      have h2 : -π * ((2 * Real.sqrt a * u) ^ 2 + (2 * Real.sqrt a * v) ^ 2) / s =
          -q * u ^ 2 + -q * v ^ 2 := by
        have hsq : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha0.le
        dsimp [q]; field_simp [hs.ne']; ring_nf; rw [hsq]; ring
      rw [h1, h2, Real.exp_add, Real.exp_add]
    unfold spinDa
    rw [hG_eq z.1 z.2, hG_eq (spinGamma a * z.1) z.2,
      hG_eq z.1 (spinGamma a * z.2), hG_eq (spinGamma a * z.1) (spinGamma a * z.2)]
    have hp1 : -p * (spinGamma a * z.1) ^ 2 = -(p * spinGamma a ^ 2) * z.1 ^ 2 := by ring
    have hp2 : -p * (spinGamma a * z.2) ^ 2 = -(p * spinGamma a ^ 2) * z.2 ^ 2 := by ring
    have hq1 : -q * (spinGamma a * z.1) ^ 2 = -(q * spinGamma a ^ 2) * z.1 ^ 2 := by ring
    have hq2 : -q * (spinGamma a * z.2) ^ 2 = -(q * spinGamma a ^ 2) * z.2 ^ 2 := by ring
    rw [hp1, hp2, hq1, hq2]
    dsimp [fp, fq]
    ring
  have hDa_int : Integrable (fun z : ℝ × ℝ =>
      |spinDa a (spinGaussTest s) z.1 z.2| * spinWc a z.1 * spinWc a z.2) volume := by
    have hprod_int : Integrable (fun z : ℝ × ℝ =>
        fp z.1 * fp z.2 - s⁻¹ * (fq z.1 * fq z.2)) volume :=
      (hfp_int.mul_prod hfp_int).sub ((hfq_int.mul_prod hfq_int).const_mul s⁻¹)
    refine hprod_int.abs.congr (Eventually.of_forall fun z => ?_)
    dsimp only
    rw [← hDa_eq z, abs_mul, abs_mul, abs_of_nonneg (spinWc_nonneg ha2 z.1),
      abs_of_nonneg (spinWc_nonneg ha2 z.2)]
  have hpt : ∀ z : ℝ × ℝ,
      fp z.1 * fp z.2 - s⁻¹ * (fq z.1 * fq z.2) ≤
        |spinDa a (spinGaussTest s) z.1 z.2| * spinWc a z.1 * spinWc a z.2 := by
    intro z
    rw [← hDa_eq z]
    calc spinDa a (spinGaussTest s) z.1 z.2 * spinWc a z.1 * spinWc a z.2
        ≤ |spinDa a (spinGaussTest s) z.1 z.2 * spinWc a z.1 * spinWc a z.2| := le_abs_self _
      _ = |spinDa a (spinGaussTest s) z.1 z.2| * spinWc a z.1 * spinWc a z.2 := by
          rw [abs_mul, abs_mul, abs_of_nonneg (spinWc_nonneg ha2 z.1),
            abs_of_nonneg (spinWc_nonneg ha2 z.2)]
  have hsub_int : Integrable (fun z : ℝ × ℝ =>
      fp z.1 * fp z.2 - s⁻¹ * (fq z.1 * fq z.2)) volume :=
    (hfp_int.mul_prod hfp_int).sub ((hfq_int.mul_prod hfq_int).const_mul s⁻¹)
  calc (spinGaussJ a (p * spinGamma a ^ 2) - spinGaussJ a p) ^ 2 -
        s⁻¹ * (spinGaussJ a (q * spinGamma a ^ 2) - spinGaussJ a q) ^ 2
      = (∫ x, fp x) * (∫ y, fp y) - s⁻¹ * ((∫ x, fq x) * (∫ y, fq y)) := by
        rw [hfp_eval, hfq_eval]; ring
    _ = ∫ z : ℝ × ℝ, (fp z.1 * fp z.2 - s⁻¹ * (fq z.1 * fq z.2)) := by
        have h1 : Integrable (fun z : ℝ × ℝ => fp z.1 * fp z.2) volume := hfp_int.mul_prod hfp_int
        have h2 : Integrable (fun z : ℝ × ℝ => s⁻¹ * (fq z.1 * fq z.2)) volume :=
          (hfq_int.mul_prod hfq_int).const_mul s⁻¹
        have hfp_prod : ∫ z : ℝ × ℝ, fp z.1 * fp z.2 = (∫ x, fp x) * (∫ y, fp y) := by
          rw [Measure.volume_eq_prod]; exact integral_prod_mul fp fp
        have hfq_prod : ∫ z : ℝ × ℝ, fq z.1 * fq z.2 = (∫ x, fq x) * (∫ y, fq y) := by
          rw [Measure.volume_eq_prod]; exact integral_prod_mul fq fq
        rw [integral_sub h1 h2, integral_const_mul, hfp_prod, hfq_prod]
    _ ≤ ∫ z : ℝ × ℝ, |spinDa a (spinGaussTest s) z.1 z.2| * spinWc a z.1 * spinWc a z.2 :=
        integral_mono hsub_int hDa_int hpt

/-- Quantitative `J_a` bounds for small `s ∈ (0, 1)` used in `spinDa_unbounded`. -/
private lemma spinGaussJ_small_s_bounds {a s R : ℝ} (ha : 2 < a) (hs : 0 < s) (hs1 : s < 1)
    (hR : 0 < R)
    (hs_pi : s ≤ π / 2)
    (hs_mq : s ≤ π * a / (2 * ((spinGamma a)⁻¹ * Real.exp (π * a / spinGamma a ^ 2)) + 2))
    (hs_gap : s ≤ π * a * ((spinGamma a ^ 2)⁻¹ - 1) / (4 * R + 4)) :
    let Mq := (spinGamma a)⁻¹ * Real.exp (π * a / spinGamma a ^ 2)
    let p := 4 * π * a * s
    let q := 4 * π * a / s
    0 ≤ spinGaussJ a q ∧ spinGaussJ a q ≤ Real.sqrt s * Mq ∧
    0 ≤ spinGaussJ a (q * spinGamma a ^ 2) ∧ spinGaussJ a (q * spinGamma a ^ 2) ≤ Real.sqrt s * Mq ∧
    Mq ≤ spinGaussJ a p ∧
    (2 * R + 2) * spinGaussJ a p ≤ spinGaussJ a (p * spinGamma a ^ 2) := by
  have ha2 : 2 ≤ a := ha.le
  have ha0 : 0 < a := by linarith
  have hγ_pos : 0 < spinGamma a := spinGamma_pos' ha
  have hγ_sq : spinGamma a ^ 2 = (a - 2) / a := spinGamma_sq' ha2
  have hγ_lt : spinGamma a < 1 := spinGamma_lt_one' ha
  have hγ_inv : 1 ≤ (spinGamma a)⁻¹ := (one_le_inv₀ hγ_pos).mpr hγ_lt.le
  set Mq := (spinGamma a)⁻¹ * Real.exp (π * a / spinGamma a ^ 2)
  set p := 4 * π * a * s
  set q := 4 * π * a / s
  have hp : 0 < p := by positivity
  have hq : 0 < q := by positivity
  have hpγ : 0 < p * spinGamma a ^ 2 := by positivity
  have hqγ : 0 < q * spinGamma a ^ 2 := by positivity
  have hexp_pA : (4 * π * a) ^ 2 / (4 * p) = π * a / s := by
    dsimp [p]; field_simp [Real.pi_pos.ne', ha0.ne', hs.ne']
  have hexp_pB : (4 * π * a * spinGamma a) ^ 2 / (4 * p) = π * a * spinGamma a ^ 2 / s := by
    dsimp [p]; field_simp [Real.pi_pos.ne', ha0.ne', hs.ne']
  have hexp_pγA : (4 * π * a) ^ 2 / (4 * (p * spinGamma a ^ 2)) =
      π * a / (s * spinGamma a ^ 2) := by
    dsimp [p]; field_simp [Real.pi_pos.ne', ha0.ne', hs.ne', hγ_pos.ne']
  have hexp_pγB : (4 * π * a * spinGamma a) ^ 2 / (4 * (p * spinGamma a ^ 2)) = π * a / s := by
    dsimp [p]; field_simp [Real.pi_pos.ne', ha0.ne', hs.ne', hγ_pos.ne']
  have hexp_qA : (4 * π * a) ^ 2 / (4 * q) = π * a * s := by
    dsimp [q]; field_simp [Real.pi_pos.ne', ha0.ne', hs.ne']
  have hexp_qγA : (4 * π * a) ^ 2 / (4 * (q * spinGamma a ^ 2)) =
      π * a * s / spinGamma a ^ 2 := by
    dsimp [q]; field_simp [Real.pi_pos.ne', ha0.ne', hs.ne', hγ_pos.ne']
  have hsqrt4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hsqrt_p : Real.sqrt (a * π / p) = (2 * Real.sqrt s)⁻¹ := by
    dsimp [p]
    have : a * π / (4 * π * a * s) = (4 * s)⁻¹ := by
      field_simp [Real.pi_pos.ne', ha0.ne', hs.ne']
    rw [this, Real.sqrt_inv, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), hsqrt4]
  have hsqrt_pγ : Real.sqrt (a * π / (p * spinGamma a ^ 2)) =
      (spinGamma a)⁻¹ * (2 * Real.sqrt s)⁻¹ := by
    rw [← div_div, Real.sqrt_div (by positivity), hsqrt_p, Real.sqrt_sq hγ_pos.le, div_eq_inv_mul]
  have hsqrt_q : Real.sqrt (a * π / q) = Real.sqrt s / 2 := by
    dsimp [q]
    have : a * π / (4 * π * a / s) = s / 4 := by
      field_simp [Real.pi_pos.ne', ha0.ne', hs.ne']
    rw [this, Real.sqrt_div hs.le, hsqrt4]
  have hsqrt_qγ : Real.sqrt (a * π / (q * spinGamma a ^ 2)) =
      (spinGamma a)⁻¹ * (Real.sqrt s / 2) := by
    rw [← div_div, Real.sqrt_div (by positivity), hsqrt_q, Real.sqrt_sq hγ_pos.le, div_eq_inv_mul]
  have hJq_nn : 0 ≤ spinGaussJ a q :=
    integral_nonneg fun x => mul_nonneg (Real.exp_pos _).le (spinWc_nonneg ha2 x)
  have hJqγ_nn : 0 ≤ spinGaussJ a (q * spinGamma a ^ 2) :=
    integral_nonneg fun x => mul_nonneg (Real.exp_pos _).le (spinWc_nonneg ha2 x)
  have hJq_le : spinGaussJ a q ≤ Real.sqrt s * Mq := by
    rw [spinGaussJ_eq ha2 hq, hsqrt_q, hexp_qA]
    have h1 : Real.exp (π * a * s) - Real.exp ((4 * π * a * spinGamma a) ^ 2 / (4 * q)) ≤
        Real.exp (π * a * s) :=
      sub_le_self _ (Real.exp_pos _).le
    have hγ2_le : spinGamma a ^ 2 ≤ 1 := by
      rw [hγ_sq]; exact (div_le_one ha0).mpr (by linarith)
    have h2 : Real.exp (π * a * s) ≤ Real.exp (π * a / spinGamma a ^ 2) := by
      refine Real.exp_le_exp.mpr ?_
      have hdiv : π * a ≤ π * a / spinGamma a ^ 2 :=
        (le_div_iff₀ (sq_pos_of_pos hγ_pos)).mpr (mul_le_of_le_one_right (by positivity) hγ2_le)
      exact (mul_le_of_le_one_right (by positivity) hs1.le).trans hdiv
    calc 2 * (Real.sqrt s / 2) *
            (Real.exp (π * a * s) - Real.exp ((4 * π * a * spinGamma a) ^ 2 / (4 * q)))
        = Real.sqrt s *
            (Real.exp (π * a * s) - Real.exp ((4 * π * a * spinGamma a) ^ 2 / (4 * q))) := by ring
      _ ≤ Real.sqrt s * Real.exp (π * a * s) := mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _)
      _ ≤ Real.sqrt s * Real.exp (π * a / spinGamma a ^ 2) :=
          mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg _)
      _ ≤ Real.sqrt s * ((spinGamma a)⁻¹ * Real.exp (π * a / spinGamma a ^ 2)) :=
          mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (Real.exp_pos _).le hγ_inv)
            (Real.sqrt_nonneg _)
      _ = Real.sqrt s * Mq := rfl
  have hJqγ_le : spinGaussJ a (q * spinGamma a ^ 2) ≤ Real.sqrt s * Mq := by
    rw [spinGaussJ_eq ha2 hqγ, hsqrt_qγ, hexp_qγA]
    have h1 : Real.exp (π * a * s / spinGamma a ^ 2) -
        Real.exp ((4 * π * a * spinGamma a) ^ 2 / (4 * (q * spinGamma a ^ 2))) ≤
        Real.exp (π * a * s / spinGamma a ^ 2) :=
      sub_le_self _ (Real.exp_pos _).le
    have h2 : Real.exp (π * a * s / spinGamma a ^ 2) ≤ Real.exp (π * a / spinGamma a ^ 2) := by
      refine Real.exp_le_exp.mpr ?_
      exact div_le_div_of_nonneg_right (mul_le_of_le_one_right (by positivity) hs1.le) (sq_nonneg _)
    calc 2 * ((spinGamma a)⁻¹ * (Real.sqrt s / 2)) *
            (Real.exp (π * a * s / spinGamma a ^ 2) -
              Real.exp ((4 * π * a * spinGamma a) ^ 2 / (4 * (q * spinGamma a ^ 2))))
        = Real.sqrt s * (spinGamma a)⁻¹ *
            (Real.exp (π * a * s / spinGamma a ^ 2) -
              Real.exp ((4 * π * a * spinGamma a) ^ 2 / (4 * (q * spinGamma a ^ 2)))) := by ring
      _ ≤ Real.sqrt s * (spinGamma a)⁻¹ * Real.exp (π * a * s / spinGamma a ^ 2) := by gcongr
      _ ≤ Real.sqrt s * (spinGamma a)⁻¹ * Real.exp (π * a / spinGamma a ^ 2) := by gcongr
      _ = Real.sqrt s * Mq := by dsimp [Mq]; ring
  have hJp_le : spinGaussJ a p ≤ (Real.sqrt s)⁻¹ * Real.exp (π * a / s) := by
    rw [spinGaussJ_eq ha2 hp, hsqrt_p, hexp_pA]
    have h1 : Real.exp (π * a / s) - Real.exp ((4 * π * a * spinGamma a) ^ 2 / (4 * p)) ≤
        Real.exp (π * a / s) :=
      sub_le_self _ (Real.exp_pos _).le
    calc 2 * (2 * Real.sqrt s)⁻¹ *
            (Real.exp (π * a / s) - Real.exp ((4 * π * a * spinGamma a) ^ 2 / (4 * p)))
        = (Real.sqrt s)⁻¹ *
            (Real.exp (π * a / s) - Real.exp ((4 * π * a * spinGamma a) ^ 2 / (4 * p))) := by
          rw [mul_inv]; ring
      _ ≤ (Real.sqrt s)⁻¹ * Real.exp (π * a / s) := by gcongr
  have hJp_ge_Mq : Mq ≤ spinGaussJ a p := by
    have hδ1 : π * a * (1 - spinGamma a ^ 2) = 2 * π := by
      rw [hγ_sq]; field_simp [ha0.ne']; ring
    have hdiff : π * a / s - π * a * spinGamma a ^ 2 / s = 2 * π / s := by
      calc π * a / s - π * a * spinGamma a ^ 2 / s
          = π * a * (1 - spinGamma a ^ 2) / s := by ring
        _ = 2 * π / s := by rw [hδ1]
    have hge2 : (2 : ℝ) ≤ Real.exp (2 * π / s) := by
      have h1 : 1 ≤ 2 * π / s := (le_div_iff₀ hs).mpr (by linarith only [hs_pi, Real.pi_pos])
      linarith only [h1, Real.add_one_le_exp (2 * π / s)]
    have hhalf : Real.exp (π * a * spinGamma a ^ 2 / s) ≤ (1 / 2 : ℝ) * Real.exp (π * a / s) := by
      have hmul : Real.exp (π * a * spinGamma a ^ 2 / s) * Real.exp (2 * π / s) =
          Real.exp (π * a / s) := by
        rw [← Real.exp_add]; congr 1; linarith only [hdiff]
      have h2 := mul_le_mul_of_nonneg_left hge2 (Real.exp_pos (π * a * spinGamma a ^ 2 / s)).le
      linarith only [hmul, h2]
    have hJp_ge : (1 / 2 : ℝ) * (Real.sqrt s)⁻¹ * Real.exp (π * a / s) ≤ spinGaussJ a p := by
      rw [spinGaussJ_eq ha2 hp, hsqrt_p, hexp_pA, hexp_pB]
      calc (1 / 2 : ℝ) * (Real.sqrt s)⁻¹ * Real.exp (π * a / s)
          = (Real.sqrt s)⁻¹ * ((1 / 2 : ℝ) * Real.exp (π * a / s)) := by ring
        _ ≤ (Real.sqrt s)⁻¹ * (Real.exp (π * a / s) - Real.exp (π * a * spinGamma a ^ 2 / s)) := by
            gcongr; linarith only [hhalf]
        _ = 2 * (2 * Real.sqrt s)⁻¹ *
              (Real.exp (π * a / s) - Real.exp (π * a * spinGamma a ^ 2 / s)) := by
            rw [mul_inv]; ring
    have hsqrt_ge : 1 ≤ (Real.sqrt s)⁻¹ := by
      rw [one_le_inv₀ (Real.sqrt_pos.mpr hs)]
      calc Real.sqrt s ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hs1.le
        _ = 1 := Real.sqrt_one
    have hexp_ge : 2 * Mq ≤ Real.exp (π * a / s) := by
      have hMq_pos : 0 < Mq := by positivity
      have h1 : 2 * Mq + 2 ≤ π * a / s := (le_div_iff₀ hs).mpr (by
        have := (le_div_iff₀ (by positivity : 0 < 2 * Mq + 2)).mp hs_mq
        linarith only [this])
      linarith only [h1, Real.add_one_le_exp (π * a / s)]
    have hMq_pos : 0 < Mq := by positivity
    calc Mq = (1 / 2 : ℝ) * 1 * (2 * Mq) := by ring
      _ ≤ (1 / 2 : ℝ) * (Real.sqrt s)⁻¹ * Real.exp (π * a / s) := by gcongr
      _ ≤ spinGaussJ a p := hJp_ge
  have hJpγ_ge : (2 * R + 2) * spinGaussJ a p ≤ spinGaussJ a (p * spinGamma a ^ 2) := by
    rw [spinGaussJ_eq ha2 hpγ, hsqrt_pγ, hexp_pγA, hexp_pγB]
    set Δ := π * a * ((spinGamma a ^ 2)⁻¹ - 1)
    have hgap : π * a / (s * spinGamma a ^ 2) - π * a / s = Δ / s := by
      dsimp [Δ]; field_simp [hs.ne', hγ_pos.ne']
    have hexp_gap : 4 * R + 4 ≤ Real.exp (Δ / s) := by
      have h1 : 4 * R + 4 ≤ Δ / s := (le_div_iff₀ hs).mpr (by
        have := (le_div_iff₀ (by positivity : 0 < 4 * R + 4)).mp hs_gap
        linarith only [this])
      linarith only [h1, Real.add_one_le_exp (Δ / s)]
    have hmul : Real.exp (π * a / s) * Real.exp (Δ / s) =
        Real.exp (π * a / (s * spinGamma a ^ 2)) := by
      rw [← Real.exp_add]; congr 1; linarith only [hgap]
    have hsub : (2 * R + 2) * Real.exp (π * a / s) ≤
        Real.exp (π * a / (s * spinGamma a ^ 2)) - Real.exp (π * a / s) := by
      have h2 := mul_le_mul_of_nonneg_left hexp_gap (Real.exp_pos (π * a / s)).le
      have hR' : (2 * R + 3) * Real.exp (π * a / s) ≤ (4 * R + 4) * Real.exp (π * a / s) :=
        mul_le_mul_of_nonneg_right (by linarith only [hR]) (Real.exp_pos _).le
      linarith only [hmul, h2, hR']
    calc (2 * R + 2) * spinGaussJ a p
        ≤ (2 * R + 2) * ((Real.sqrt s)⁻¹ * Real.exp (π * a / s)) :=
          mul_le_mul_of_nonneg_left hJp_le (by positivity)
      _ = (Real.sqrt s)⁻¹ * ((2 * R + 2) * Real.exp (π * a / s)) := by ring
      _ ≤ (Real.sqrt s)⁻¹ *
            (Real.exp (π * a / (s * spinGamma a ^ 2)) - Real.exp (π * a / s)) := by gcongr
      _ ≤ (spinGamma a)⁻¹ * ((Real.sqrt s)⁻¹ *
            (Real.exp (π * a / (s * spinGamma a ^ 2)) - Real.exp (π * a / s))) :=
          le_mul_of_one_le_left
            (mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))
              (le_trans (mul_nonneg (by linarith only [hR]) (Real.exp_pos (π * a / s)).le) hsub))
            hγ_inv
      _ = 2 * ((spinGamma a)⁻¹ * (2 * Real.sqrt s)⁻¹) *
            (Real.exp (π * a / (s * spinGamma a ^ 2)) - Real.exp (π * a / s)) := by
          rw [mul_inv]; ring
  exact ⟨hJq_nn, hJq_le, hJqγ_nn, hJqγ_le, hJp_ge_Mq, hJpγ_ge⟩

/-- Unboundedness of `‖D_a G‖_{L¹(w_c ⊗ w_c)} / M_2[Φ]` on `\overline{\mathcal A}_{\rm spin}`
(`spinning_foundations.tex`, Lemma S2.2). -/
theorem spinDa_unbounded {a : ℝ} (ha : 2 < a) (K : ℝ) :
    ∃ Φ : ℝ × ℝ → ℝ, SpinTestClass a Φ ∧ 0 < spinM2 a Φ ∧
      K * spinM2 a Φ < ∫ p : ℝ × ℝ, |spinDa a Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2 := by
  have ha2 : 2 ≤ a := ha.le
  have ha0 : 0 < a := by linarith
  have hγ_pos : 0 < spinGamma a := spinGamma_pos' ha
  have hγ_sq : spinGamma a ^ 2 = (a - 2) / a := spinGamma_sq' ha2
  set Δ : ℝ := π * a * ((spinGamma a ^ 2)⁻¹ - 1)
  have hΔ_pos : 0 < Δ := by
    dsimp [Δ]
    have h1 : 1 < (spinGamma a ^ 2)⁻¹ := by
      rw [hγ_sq, inv_div, one_lt_div (by linarith : 0 < a - 2)]; linarith
    have : 0 < (spinGamma a ^ 2)⁻¹ - 1 := sub_pos.mpr h1
    positivity
  set Mq : ℝ := (spinGamma a)⁻¹ * Real.exp (π * a / spinGamma a ^ 2)
  have hMq_pos : 0 < Mq := by positivity
  set R : ℝ := max (2 : ℝ) (2 * (max K 0 + 2) + 2)
  have hR_pos : 0 < R := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  set s : ℝ := min (1 / 2 : ℝ) (min (π / 2) (min (π * a / (2 * Mq + 2)) (Δ / (4 * R + 4))))
  have hs_pos : 0 < s := by
    dsimp [s]
    exact lt_min (by norm_num) (lt_min (div_pos Real.pi_pos two_pos)
      (lt_min (div_pos (mul_pos Real.pi_pos ha0) (by linarith))
        (div_pos hΔ_pos (by linarith))))
  have hs_lt1 : s < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hs_pi : s ≤ π / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hs_mq : s ≤ π * a / (2 * Mq + 2) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hs_gap : s ≤ Δ / (4 * R + 4) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hJq_nn, hJq_le, hJqγ_nn, hJqγ_le, hJp_ge_Mq, hJpγ_ge⟩ :=
    spinGaussJ_small_s_bounds ha hs_pos hs_lt1 hR_pos hs_pi hs_mq hs_gap
  set p := 4 * π * a * s
  set q := 4 * π * a / s
  have hJp_pos : 0 < spinGaussJ a p := hMq_pos.trans_le hJp_ge_Mq
  have hM2_pos := spinGaussTest_M2_pos ha hs_pos hs_lt1
  refine ⟨spinGaussTest s, spinGaussTest_mem_SpinTestClass ha2 hs_pos, hM2_pos, ?_⟩
  have hMq_sq : Mq ^ 2 ≤ spinGaussJ a p ^ 2 := pow_le_pow_left₀ hMq_pos.le hJp_ge_Mq 2
  have hM2_le : spinM2 a (spinGaussTest s) ≤ 2 * spinGaussJ a p ^ 2 := by
    have hq_sq : s⁻¹ * spinGaussJ a q ^ 2 ≤ Mq ^ 2 := by
      have h1 : spinGaussJ a q ^ 2 ≤ (Real.sqrt s * Mq) ^ 2 :=
        pow_le_pow_left₀ hJq_nn hJq_le 2
      rw [mul_pow, Real.sq_sqrt hs_pos.le] at h1
      calc s⁻¹ * spinGaussJ a q ^ 2 ≤ s⁻¹ * (s * Mq ^ 2) :=
            mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hs_pos.le)
        _ = Mq ^ 2 := by field_simp [hs_pos.ne']
    linarith only [spinGaussTest_M2_le ha2 hs_pos, hq_sq, hMq_sq]
  have hq_diff_le : s⁻¹ * (spinGaussJ a (q * spinGamma a ^ 2) - spinGaussJ a q) ^ 2 ≤
      spinGaussJ a p ^ 2 := by
    have habs : |spinGaussJ a (q * spinGamma a ^ 2) - spinGaussJ a q| ≤ Real.sqrt s * Mq := by
      rw [abs_le]; constructor <;> linarith only [hJq_nn, hJq_le, hJqγ_nn, hJqγ_le]
    have hsq : (spinGaussJ a (q * spinGamma a ^ 2) - spinGaussJ a q) ^ 2 ≤
        (Real.sqrt s * Mq) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) habs 2
    rw [mul_pow, Real.sq_sqrt hs_pos.le] at hsq
    have h1 : s⁻¹ * (spinGaussJ a (q * spinGamma a ^ 2) - spinGaussJ a q) ^ 2 ≤ Mq ^ 2 := by
      calc s⁻¹ * (spinGaussJ a (q * spinGamma a ^ 2) - spinGaussJ a q) ^ 2
          ≤ s⁻¹ * (s * Mq ^ 2) := mul_le_mul_of_nonneg_left hsq (inv_nonneg.mpr hs_pos.le)
        _ = Mq ^ 2 := by field_simp [hs_pos.ne']
    exact h1.trans hMq_sq
  have hp_diff_ge : (2 * R + 1) ^ 2 * spinGaussJ a p ^ 2 ≤
      (spinGaussJ a (p * spinGamma a ^ 2) - spinGaussJ a p) ^ 2 := by
    have h1 : (2 * R + 1) * spinGaussJ a p ≤
        spinGaussJ a (p * spinGamma a ^ 2) - spinGaussJ a p := by
      linarith only [hJpγ_ge]
    have hsq := pow_le_pow_left₀ (by positivity) h1 2
    rwa [mul_pow] at hsq
  have hKM2 : K * spinM2 a (spinGaussTest s) ≤ 2 * max K 0 * spinGaussJ a p ^ 2 := by
    calc K * spinM2 a (spinGaussTest s)
        ≤ max K 0 * spinM2 a (spinGaussTest s) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hM2_pos.le
      _ ≤ max K 0 * (2 * spinGaussJ a p ^ 2) :=
          mul_le_mul_of_nonneg_left hM2_le (le_max_right _ _)
      _ = 2 * max K 0 * spinGaussJ a p ^ 2 := by ring
  have hstrict : 2 * max K 0 * spinGaussJ a p ^ 2 <
      ((2 * R + 1) ^ 2 - 1) * spinGaussJ a p ^ 2 := by
    have hKR : 2 * (max K 0 + 2) + 2 ≤ R := le_max_right _ _
    have hlt : 2 * max K 0 < (2 * R + 1) ^ 2 - 1 := by
      have h0 : 0 ≤ max K 0 := le_max_right _ _
      nlinarith only [hKR, h0]
    exact mul_lt_mul_of_pos_right hlt (sq_pos_of_pos hJp_pos)
  linarith only [hKM2, hstrict, hp_diff_ge, hq_diff_le, spinGaussTest_Da_ge ha hs_pos]

/-! ### Part 3: Full assembly of Lemma S2.2 (`spinnotes:S22`) -/

/-- **Lemma S2.2 (`spinnotes:S22`)**: uniform bistrip bound, separate holomorphy on `S_{1/2}²`,
real agreement, outward `L¹` bound `≤ (1 + λ⁻¹)² M_2[Φ]`, and unboundedness of the inward
`L¹(w_c ⊗ w_c)` norm on `\overline{\mathcal A}_{\rm spin}`. -/
theorem spinS22 : SpinS22 := by
  intro c hc
  have ha_gt2 : 2 < (c - 1) / 12 := by linarith
  have ha2 : 2 ≤ (c - 1) / 12 := ha_gt2.le
  refine ⟨fun {Φ} hΦ => ?_, fun K => spinDa_unbounded ha_gt2 K⟩
  refine ⟨fun bR hbR => differentiableOn_spinDaC_left ha2 hΦ hbR,
    fun bL hbL => differentiableOn_spinDaC_right ha2 hΦ hbL,
    fun xL xR => spinDaC_eq_spinDa ha2 hΦ xL xR,
    fun bL bR hbL hbR => norm_spinDaC_le ha2 hΦ hbL hbR,
    (integrable_and_integral_spinDeltaA_wc ha_gt2 hΦ).1,
    (integrable_and_integral_spinDeltaA_wc ha_gt2 hΦ).2⟩

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.Spin.integrable_and_integral_spinDeltaA_wc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.integrable_and_integral_spinDeltaA_wc

/-- info: 'FormalResearch.ModularBootstrap.Spin.spinGaussTest_mem_SpinTestClass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spinGaussTest_mem_SpinTestClass

/-- info: 'FormalResearch.ModularBootstrap.Spin.spinDa_unbounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spinDa_unbounded

/-- info: 'FormalResearch.ModularBootstrap.Spin.spinS22' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spinS22

end FormalResearch.ModularBootstrap.Spin
