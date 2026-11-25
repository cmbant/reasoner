module

public import FormalResearch.SignUncertainty.DeepLobeKernel
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The `τ`-integral of the lobe weight (`lem:radial-compactness`, Step 2)

`∫_ℝ (2 + |τ|)^{1/2} exp(-k u(τ)) dτ ≤ 9 / √k` for `k ≥ 3`, with `u = lobeU` (`lobe_integral_le`):
on `|τ| ≤ 1` the integrand is at most `√3 e^{-kτ²/2}` and on `|τ| > 1` at most `√3 e^{-k/2} |τ|^{1/2-k}`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

lemma integrable_comp_abs_of_Ioi {f : ℝ → ℝ} (hf : IntegrableOn (fun x => f |x|) (Ioi 0)) :
    Integrable (fun x : ℝ => f |x|) := by
  have int_Iic : IntegrableOn (fun x ↦ f |x|) (Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding fun x : ℝ => -x := (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp_rw [Function.comp_def, abs_neg, neg_preimage, neg_Iic, neg_zero]
    exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hf
  have := int_Iic.union hf
  rwa [Iic_union_Ioi, integrableOn_univ] at this

/-- The one-sided profile `F₀(x) = (2 + x)^{1/2} exp(-k u(x))`. -/
noncomputable def lobeF0 (k x : ℝ) : ℝ := (2 + x) ^ (1 / 2 : ℝ) * Real.exp (-(k * lobeU x))

lemma lobeU_abs (τ : ℝ) : lobeU |τ| = lobeU τ := by simp [lobeU, sq_abs, abs_abs]

lemma lobeF0_le {k x : ℝ} (_hk : 0 ≤ k) (hx : 0 < x) :
    lobeF0 k x ≤ Real.sqrt 3 * Real.exp (-(k / 2) * x ^ 2) +
      (Ioi (1 : ℝ)).indicator (fun x : ℝ => Real.sqrt 3 * Real.exp (-(k / 2)) * x ^ (1 / 2 - k)) x := by
  unfold lobeF0
  rcases le_or_gt x 1 with h | h
  · have hU : lobeU x = x ^ 2 / 2 := by
      have h1 : min (x ^ 2) 1 = x ^ 2 := min_eq_left (by nlinarith)
      have h2 : max 0 (Real.log |x|) = 0 := max_eq_left (by
        rw [abs_of_pos hx]; exact Real.log_nonpos hx.le h)
      unfold lobeU; rw [h1, h2]; ring
    have hind : (Ioi (1 : ℝ)).indicator (fun x : ℝ => Real.sqrt 3 * Real.exp (-(k / 2)) * x ^ (1 / 2 - k)) x = 0 :=
      Set.indicator_of_notMem (by simpa using h) _
    rw [hind, add_zero, hU]
    have h2 : (2 + x) ^ (1 / 2 : ℝ) ≤ Real.sqrt 3 := by
      rw [← Real.sqrt_eq_rpow]; exact Real.sqrt_le_sqrt (by linarith)
    have h3 : Real.exp (-(k * (x ^ 2 / 2))) = Real.exp (-(k / 2) * x ^ 2) := by congr 1; ring
    rw [h3]
    exact mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
  · have hU : lobeU x = 1 / 2 + Real.log x := by
      have h1 : min (x ^ 2) 1 = 1 := min_eq_right (by nlinarith)
      have h2 : max 0 (Real.log |x|) = Real.log x := by
        rw [abs_of_pos hx]; exact max_eq_right (Real.log_nonneg h.le)
      unfold lobeU; rw [h1, h2]; ring
    have hind : (Ioi (1 : ℝ)).indicator (fun x : ℝ => Real.sqrt 3 * Real.exp (-(k / 2)) * x ^ (1 / 2 - k)) x =
        Real.sqrt 3 * Real.exp (-(k / 2)) * x ^ (1 / 2 - k) := Set.indicator_of_mem h _
    rw [hind, hU]
    have h2 : (2 + x) ^ (1 / 2 : ℝ) ≤ Real.sqrt 3 * x ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, ← Real.sqrt_mul (by norm_num)]
      exact Real.sqrt_le_sqrt (by linarith)
    have h3 : Real.exp (-(k * (1 / 2 + Real.log x))) = Real.exp (-(k / 2)) * x ^ (-k) := by
      rw [Real.rpow_def_of_pos hx, ← Real.exp_add]; congr 1; ring
    have h4 : x ^ (1 / 2 - k) = x ^ (1 / 2 : ℝ) * x ^ (-k) := by
      rw [← Real.rpow_add hx]; congr 1
    have hnn : 0 ≤ Real.exp (-(k / 2)) * x ^ (-k) := by positivity
    calc (2 + x) ^ (1 / 2 : ℝ) * Real.exp (-(k * (1 / 2 + Real.log x)))
        = (2 + x) ^ (1 / 2 : ℝ) * (Real.exp (-(k / 2)) * x ^ (-k)) := by rw [h3]
      _ ≤ (Real.sqrt 3 * x ^ (1 / 2 : ℝ)) * (Real.exp (-(k / 2)) * x ^ (-k)) :=
          mul_le_mul_of_nonneg_right h2 hnn
      _ = Real.sqrt 3 * Real.exp (-(k / 2)) * x ^ (1 / 2 - k) := by rw [h4]; ring
      _ ≤ _ := le_add_of_nonneg_left (by positivity)

/-- `∫ (2 + |τ|)^{1/2} exp(-k u(τ)) dτ ≤ 9 / √k` for `k ≥ 3`. -/
theorem lobe_integral_le {k : ℝ} (hk : 3 ≤ k) :
    Integrable (fun τ : ℝ => (2 + |τ|) ^ (1 / 2 : ℝ) * Real.exp (-(k * lobeU τ))) ∧
      ∫ τ : ℝ, (2 + |τ|) ^ (1 / 2 : ℝ) * Real.exp (-(k * lobeU τ)) ≤ 9 / Real.sqrt k := by
  have hk0 : 0 < k := by linarith
  have hF : (fun τ : ℝ => (2 + |τ|) ^ (1 / 2 : ℝ) * Real.exp (-(k * lobeU τ))) =
      fun τ => lobeF0 k |τ| := by
    funext τ; simp [lobeF0, lobeU_abs]
  rw [hF]
  -- majorant on `Ioi 0`
  set G1 : ℝ → ℝ := fun x => Real.sqrt 3 * Real.exp (-(k / 2) * x ^ 2) with hG1
  set G2 : ℝ → ℝ := (Ioi (1 : ℝ)).indicator
    (fun x : ℝ => Real.sqrt 3 * Real.exp (-(k / 2)) * x ^ (1 / 2 - k)) with hG2
  have hG1i : IntegrableOn G1 (Ioi 0) := by
    have := (integrable_exp_neg_mul_sq (by linarith : 0 < k / 2)).const_mul (Real.sqrt 3)
    exact this.integrableOn
  have hG2g : IntegrableOn (fun x : ℝ => Real.sqrt 3 * Real.exp (-(k / 2)) * x ^ (1 / 2 - k)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos).const_mul _
  have hG2i : IntegrableOn G2 (Ioi 0) :=
    ((integrable_indicator_iff measurableSet_Ioi).mpr hG2g).integrableOn
  have hmeas : Measurable (lobeF0 k) := by
    unfold lobeF0 lobeU
    measurability
  have hF0nn : ∀ x : ℝ, 0 < x → 0 ≤ lobeF0 k x := fun x hx => by
    unfold lobeF0
    have : 0 < 2 + x := by linarith
    positivity
  have hF0le : ∀ x ∈ Ioi (0 : ℝ), ‖lobeF0 k x‖ ≤ G1 x + G2 x := fun x hx => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hF0nn x hx)]
    exact lobeF0_le hk0.le hx
  have hF0i : IntegrableOn (lobeF0 k) (Ioi 0) :=
    Integrable.mono' (hG1i.add hG2i) hmeas.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall hF0le))
  have hF0abs : IntegrableOn (fun x : ℝ => lobeF0 k |x|) (Ioi 0) :=
    hF0i.congr_fun (fun x hx => by simp [abs_of_pos (show (0 : ℝ) < x from hx)]) measurableSet_Ioi
  refine ⟨integrable_comp_abs_of_Ioi hF0abs, ?_⟩
  rw [integral_comp_abs]
  have hint : ∫ x in Ioi (0 : ℝ), lobeF0 k x ≤ ∫ x in Ioi (0 : ℝ), (G1 x + G2 x) :=
    setIntegral_mono_on hF0i (hG1i.add hG2i) measurableSet_Ioi (fun x hx => by
      have := hF0le x hx
      rwa [Real.norm_eq_abs, abs_of_nonneg (hF0nn x hx)] at this)
  rw [integral_add hG1i hG2i] at hint
  have e1 : ∫ x in Ioi (0 : ℝ), G1 x = Real.sqrt 3 * (Real.sqrt (Real.pi / (k / 2)) / 2) := by
    rw [hG1, integral_const_mul, integral_gaussian_Ioi]
  have e2 : ∫ x in Ioi (0 : ℝ), G2 x = Real.sqrt 3 * Real.exp (-(k / 2)) * (1 / (k - 3 / 2)) := by
    rw [hG2, setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi, max_eq_right zero_le_one,
      integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) one_pos]
    have : (1 / 2 - k + 1 : ℝ) = -(k - 3 / 2) := by ring
    rw [this, Real.one_rpow]
    have hne : (k - 3 / 2) ≠ 0 := by intro h; linarith
    field_simp
  rw [e1, e2] at hint
  -- numerics
  have hr : 0 < Real.sqrt k := Real.sqrt_pos.mpr hk0
  have hr3 : Real.sqrt 3 ≤ Real.sqrt k := Real.sqrt_le_sqrt hk
  have hsq : Real.sqrt k * Real.sqrt k = k := Real.mul_self_sqrt hk0.le
  have hA : Real.sqrt 3 * Real.sqrt (Real.pi / (k / 2)) ≤ 4.4 / Real.sqrt k := by
    have h1 : Real.sqrt (Real.pi / (k / 2)) = Real.sqrt (2 * Real.pi) / Real.sqrt k := by
      rw [show Real.pi / (k / 2) = 2 * Real.pi / k by field_simp, Real.sqrt_div (by positivity)]
    rw [h1, ← mul_div_assoc, ← Real.sqrt_mul (by norm_num), div_le_div_iff_of_pos_right hr]
    rw [Real.sqrt_le_left (by norm_num)]
    nlinarith [Real.pi_lt_d2]
  have hB : 2 * (Real.sqrt 3 * Real.exp (-(k / 2)) * (1 / (k - 3 / 2))) ≤ 4 / Real.sqrt k := by
    have he : Real.exp (-(k / 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hk2 : 0 < k - 3 / 2 := by linarith
    have h1 : 1 / (k - 3 / 2) ≤ 2 / k := by
      rw [div_le_div_iff₀ hk2 hk0]; linarith
    have h2 : 2 * (Real.sqrt 3 * Real.exp (-(k / 2)) * (1 / (k - 3 / 2))) ≤
        2 * (Real.sqrt 3 * 1 * (2 / k)) := by gcongr
    refine h2.trans ?_
    rw [show 2 * (Real.sqrt 3 * 1 * (2 / k)) = 4 * Real.sqrt 3 / k by ring,
      div_le_div_iff₀ hk0 hr]
    nlinarith [mul_le_mul_of_nonneg_left hr3 (by norm_num : (0 : ℝ) ≤ 4), hsq]
  have hhalf : Real.sqrt 3 * (Real.sqrt (Real.pi / (k / 2)) / 2) = (Real.sqrt 3 * Real.sqrt (Real.pi / (k / 2))) / 2 := by
    ring
  rw [hhalf] at hint
  have : 2 * ∫ x in Ioi (0 : ℝ), lobeF0 k x ≤ 9 / Real.sqrt k := by
    have hc : 8.4 / Real.sqrt k ≤ 9 / Real.sqrt k := by gcongr; norm_num
    have hd : 4.4 / Real.sqrt k + 4 / Real.sqrt k = 8.4 / Real.sqrt k := by ring
    nlinarith [hA, hB, hint, hc, hd]
  exact this

/-- info: 'FormalResearch.SignUncertainty.lobe_integral_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lobe_integral_le

end FormalResearch.SignUncertainty
