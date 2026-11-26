module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Elementary integral bounds for the steepest-descent moments (`ct:cfu` Step 3)

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:cfu`, Step 3 (`ct:sd-moments`).  **Proved.**
Gamma-function evaluations of `∫₀^∞ t^α e^{-lam t}`, `∫₀^∞ t^β e^{-b t²}`, `∫₀^∞ t^α e^{-b t³}`, and the comparison of an interval
integral with the half-line integral of a dominating function.
-/

@[expose] public section

open Set Filter Topology MeasureTheory Real

namespace FormalResearch.SignUncertainty.CtSd

lemma integral_lin {α lam : ℝ} (hα : -1 < α) (hlam : 0 < lam) :
    ∫ t in Ioi (0 : ℝ), t ^ α * Real.exp (-(lam * t)) = lam ^ (-(α + 1)) * Real.Gamma (α + 1) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 1) (q := α) (b := lam) one_pos hα hlam
  simp only [Real.rpow_one, div_one, mul_one, one_div, inv_one] at h
  have e : ∀ t : ℝ, Real.exp (-lam * t) = Real.exp (-(lam * t)) := fun t => by ring_nf
  simp_rw [e] at h
  exact h

lemma integrableOn_lin {α lam : ℝ} (hα : -1 < α) (hlam : 0 < lam) :
    IntegrableOn (fun t : ℝ => t ^ α * Real.exp (-(lam * t))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := α) (b := lam) hα one_pos hlam
  refine h.congr_fun (fun t ht => ?_) measurableSet_Ioi
  simp only [Real.rpow_one]
  ring_nf

lemma integral_sq {β b : ℝ} (hβ : -1 < β) (hb : 0 < b) :
    ∫ t in Ioi (0 : ℝ), t ^ β * Real.exp (-(b * t ^ 2)) = b ^ (-(β + 1) / 2) * (1 / 2) * Real.Gamma ((β + 1) / 2) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := β) (b := b) two_pos hβ hb
  have e : ∀ t : ℝ, Real.exp (-b * t ^ (2 : ℝ)) = Real.exp (-(b * t ^ 2)) := fun t => by
    rw [Real.rpow_two]; ring_nf
  simp_rw [e] at h
  exact h

lemma integrableOn_sq {β b : ℝ} (hβ : -1 < β) (hb : 0 < b) :
    IntegrableOn (fun t : ℝ => t ^ β * Real.exp (-(b * t ^ 2))) (Ioi 0) := by
  refine (integrableOn_rpow_mul_exp_neg_mul_sq hb hβ).congr_fun (fun t ht => ?_) measurableSet_Ioi
  ring_nf

lemma integral_cube {α b : ℝ} (hα : -1 < α) (hb : 0 < b) :
    ∫ t in Ioi (0 : ℝ), t ^ α * Real.exp (-(b * t ^ 3)) = b ^ (-(α + 1) / 3) * (1 / 3) * Real.Gamma ((α + 1) / 3) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 3) (q := α) (b := b) (by norm_num) hα hb
  have e : ∀ t : ℝ, Real.exp (-b * t ^ (3 : ℝ)) = Real.exp (-(b * t ^ 3)) := fun t => by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring_nf
  simp_rw [e] at h
  exact h

lemma integrableOn_cube {α b : ℝ} (hα : -1 < α) (hb : 0 < b) :
    IntegrableOn (fun t : ℝ => t ^ α * Real.exp (-(b * t ^ 3))) (Ioi 0) := by
  refine (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 3) (s := α) (b := b) hα (by norm_num) hb).congr_fun
    (fun t ht => ?_) measurableSet_Ioi
  dsimp only
  rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring_nf

/-- An interval integral over `[a,b] ⊂ [0,∞)` of a nonnegative function dominated by an integrable `g` is at most `∫_{(0,∞)} g`. -/
lemma intervalIntegral_le_Ioi {f g : ℝ → ℝ} {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hf0 : ∀ t, 0 < t → 0 ≤ f t) (hfg : ∀ t, 0 < t → f t ≤ g t) (hg : IntegrableOn g (Ioi 0))
    (hfm : AEStronglyMeasurable f (volume.restrict (Ioc a b))) :
    ∫ t in a..b, f t ≤ ∫ t in Ioi (0 : ℝ), g t := by
  rw [intervalIntegral.integral_of_le hab]
  have hsub : Ioc a b ⊆ Ioi 0 := fun t ht => lt_of_le_of_lt ha ht.1
  have hgi : IntegrableOn g (Ioc a b) := hg.mono_set hsub
  have hfi : IntegrableOn f (Ioc a b) := by
    refine hgi.mono' hfm ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have := hsub ht
    rw [Real.norm_eq_abs, abs_of_nonneg (hf0 t this)]
    exact hfg t this
  calc ∫ t in Ioc a b, f t ≤ ∫ t in Ioc a b, g t :=
        setIntegral_mono_on hfi hgi measurableSet_Ioc (fun t ht => hfg t (hsub ht))
    _ ≤ ∫ t in Ioi (0 : ℝ), g t := by
        refine setIntegral_mono_set hg ?_ (ae_of_all _ fun x hx => hsub hx)
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact (hf0 t ht).trans (hfg t ht)

/-- Variant of `intervalIntegral_le_Ioi` with the domination only on `(a,b]`. -/
lemma intervalIntegral_le_Ioi' {f g : ℝ → ℝ} {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hf0 : ∀ t ∈ Ioc a b, 0 ≤ f t) (hfg : ∀ t ∈ Ioc a b, f t ≤ g t) (hg0 : ∀ t, 0 < t → 0 ≤ g t)
    (hg : IntegrableOn g (Ioi 0))
    (hfm : AEStronglyMeasurable f (volume.restrict (Ioc a b))) :
    ∫ t in a..b, f t ≤ ∫ t in Ioi (0 : ℝ), g t := by
  rw [intervalIntegral.integral_of_le hab]
  have hsub : Ioc a b ⊆ Ioi 0 := fun t ht => lt_of_le_of_lt ha ht.1
  have hgi : IntegrableOn g (Ioc a b) := hg.mono_set hsub
  have hfi : IntegrableOn f (Ioc a b) := by
    refine hgi.mono' hfm ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (hf0 t ht)]
    exact hfg t ht
  calc ∫ t in Ioc a b, f t ≤ ∫ t in Ioc a b, g t :=
        setIntegral_mono_on hfi hgi measurableSet_Ioc (fun t ht => hfg t ht)
    _ ≤ ∫ t in Ioi (0 : ℝ), g t := by
        refine setIntegral_mono_set hg ?_ (ae_of_all _ fun x hx => hsub hx)
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact hg0 t ht

/-- Variant with the half-line `(a₀, ∞)`, `a₀ ≤ a`. -/
lemma intervalIntegral_le_IoiFrom {f g : ℝ → ℝ} {a₀ a b : ℝ} (ha : a₀ ≤ a) (hab : a ≤ b)
    (hf0 : ∀ t ∈ Ioc a b, 0 ≤ f t) (hfg : ∀ t ∈ Ioc a b, f t ≤ g t) (hg0 : ∀ t, a₀ < t → 0 ≤ g t)
    (hg : IntegrableOn g (Ioi a₀))
    (hfm : AEStronglyMeasurable f (volume.restrict (Ioc a b))) :
    ∫ t in a..b, f t ≤ ∫ t in Ioi a₀, g t := by
  rw [intervalIntegral.integral_of_le hab]
  have hsub : Ioc a b ⊆ Ioi a₀ := fun t ht => lt_of_le_of_lt ha ht.1
  have hgi : IntegrableOn g (Ioc a b) := hg.mono_set hsub
  have hfi : IntegrableOn f (Ioc a b) := by
    refine hgi.mono' hfm ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (hf0 t ht)]
    exact hfg t ht
  calc ∫ t in Ioc a b, f t ≤ ∫ t in Ioc a b, g t :=
        setIntegral_mono_on hfi hgi measurableSet_Ioc (fun t ht => hfg t ht)
    _ ≤ ∫ t in Ioi a₀, g t := by
        refine setIntegral_mono_set hg ?_ (ae_of_all _ fun x hx => hsub hx)
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact hg0 t ht

end FormalResearch.SignUncertainty.CtSd
