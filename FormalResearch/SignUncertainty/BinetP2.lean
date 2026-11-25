module

public import FormalResearch.Asymptotics.BinetRemainder
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The periodic function `P₂` and the Laplace representation of the Binet kernel

`P₂(s) = {s}(1-{s})/2`.  **Proved**: for `t > 0`, `∫₀^∞ e^{-ts} P₂(s) ds = μ_Bin(t)/t`
(split `(0,∞) = (0,1] ∪ (1,∞)`, shift by one period, explicit antiderivative on `[0,1]`).
This is the first step of the vertical-line decay of the Binet remainder
(`constant_terms_lower.tex`, `ct:dual-id` (1)).
-/

@[expose] public section

open Filter MeasureTheory Set Topology
open FormalResearch.Asymptotics

namespace FormalResearch.SignUncertainty.BinetDecay

/-- `P₂(s) = {s}(1-{s})/2`, the periodic Bernoulli-type function. -/
noncomputable def binP2 (s : ℝ) : ℝ := Int.fract s * (1 - Int.fract s) / 2

lemma binP2_nonneg (s : ℝ) : 0 ≤ binP2 s := by
  unfold binP2
  have h0 := Int.fract_nonneg s
  have h1 := Int.fract_lt_one s
  have : 0 ≤ 1 - Int.fract s := by linarith
  positivity

lemma binP2_le (s : ℝ) : binP2 s ≤ 1 / 8 := by
  unfold binP2
  nlinarith [sq_nonneg (Int.fract s - 1 / 2)]

lemma abs_binP2_le (s : ℝ) : |binP2 s| ≤ 1 / 8 := by
  rw [abs_of_nonneg (binP2_nonneg s)]; exact binP2_le s

lemma measurable_binP2 : Measurable binP2 := by
  unfold binP2
  exact (measurable_fract.mul (measurable_const.sub measurable_fract)).div_const 2

lemma binP2_add_one (s : ℝ) : binP2 (s + 1) = binP2 s := by
  simp [binP2, Int.fract_add_one]

lemma binP2_of_mem {s : ℝ} (h0 : 0 ≤ s) (h1 : s < 1) : binP2 s = s * (1 - s) / 2 := by
  unfold binP2
  rw [Int.fract_eq_self.mpr ⟨h0, h1⟩]

lemma integrableOn_exp_mul_binP2 {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun s : ℝ => Real.exp (-(t * s)) * binP2 s) (Ioi 0) := by
  have hI : IntegrableOn (fun s : ℝ => (1 / 8 : ℝ) * Real.exp (-t * s)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 ht).const_mul _
  refine hI.mono' ?_ ?_
  · exact ((Real.continuous_exp.comp (by fun_prop)).measurable.mul measurable_binP2).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s _ => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have : Real.exp (-(t * s)) = Real.exp (-t * s) := by rw [neg_mul]
    rw [this, mul_comm]
    exact mul_le_mul_of_nonneg_right (abs_binP2_le s) (Real.exp_pos _).le

/-- Shift by one period. -/
lemma integral_Ioi_one_shift (t : ℝ) :
    ∫ s in Ioi (1 : ℝ), Real.exp (-(t * s)) * binP2 s =
      Real.exp (-t) * ∫ s in Ioi (0 : ℝ), Real.exp (-(t * s)) * binP2 s := by
  have h := (measurePreserving_add_right volume (1 : ℝ)).setIntegral_preimage_emb
    (measurableEmbedding_addRight (1 : ℝ)) (fun s : ℝ => Real.exp (-(t * s)) * binP2 s) (Ioi 1)
  have hpre : (fun x : ℝ => x + 1) ⁻¹' Ioi 1 = Ioi 0 := by
    ext x; simp
  rw [hpre] at h
  rw [← h, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  simp only [binP2_add_one]
  rw [show -(t * (s + 1)) = -t + -(t * s) by ring, Real.exp_add]
  ring


/-- The integral over one period, in closed form. -/
lemma integral_unit_period {t : ℝ} (ht : 0 < t) :
    ∫ s in Ioc (0 : ℝ) 1, Real.exp (-(t * s)) * binP2 s =
      Real.exp (-t) * (1 / t ^ 3 - 1 / (2 * t ^ 2) + (1 / t ^ 2 - 1 / (2 * t)) + 1 / (2 * t)) -
        (1 / t ^ 3 - 1 / (2 * t ^ 2)) := by
  have ht0 : t ≠ 0 := ht.ne'
  obtain ⟨α, hα⟩ : ∃ α : ℝ, α = 1 / t ^ 3 - 1 / (2 * t ^ 2) := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = 1 / t ^ 2 - 1 / (2 * t) := ⟨_, rfl⟩
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ, γ = 1 / (2 * t) := ⟨_, rfl⟩
  rw [← hα, ← hβ, ← hγ]
  have hH : ∀ s : ℝ, HasDerivAt (fun s : ℝ => Real.exp (-(t * s)) * (α + β * s + γ * s ^ 2))
      (Real.exp (-(t * s)) * (s * (1 - s) / 2)) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => Real.exp (-(t * s))) (Real.exp (-(t * s)) * (-t)) s := by
      have := ((hasDerivAt_id s).const_mul t).neg.exp
      simpa using this
    have h2 : HasDerivAt (fun s : ℝ => α + β * s + γ * s ^ 2) (β + γ * (2 * s)) s := by
      have := (((hasDerivAt_id s).const_mul β).const_add α).fun_add ((hasDerivAt_pow 2 s).const_mul γ)
      simpa using this
    refine (h1.mul h2).congr_deriv ?_
    have e1 : -t * γ = -(1 / 2) := by rw [hγ]; field_simp
    have e2 : 2 * γ - t * β = 1 / 2 := by rw [hγ, hβ]; field_simp; ring
    have e3 : β - t * α = 0 := by rw [hα, hβ]; field_simp; ring
    have : Real.exp (-(t * s)) * (-t) * (α + β * s + γ * s ^ 2) + Real.exp (-(t * s)) * (β + γ * (2 * s)) =
        Real.exp (-(t * s)) * ((β - t * α) + (2 * γ - t * β) * s + (-t * γ) * s ^ 2) := by ring
    rw [this, e1, e2, e3]; ring
  have hcongr : ∫ s in Ioc (0 : ℝ) 1, Real.exp (-(t * s)) * binP2 s =
      ∫ s in (0 : ℝ)..1, Real.exp (-(t * s)) * (s * (1 - s) / 2) := by
    rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo,
      integral_Ioc_eq_integral_Ioo (f := fun s : ℝ => Real.exp (-(t * s)) * (s * (1 - s) / 2))]
    refine setIntegral_congr_fun measurableSet_Ioo fun s hs => ?_
    rw [binP2_of_mem hs.1.le hs.2]
  rw [hcongr, intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hH s)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  simp


/-- **Laplace representation of the Binet kernel.**  For `t > 0`,
`∫₀^∞ e^{-ts} P₂(s) ds = μ_Bin(t)/t`. -/
theorem laplace_binP2 {t : ℝ} (ht : 0 < t) :
    ∫ s in Ioi (0 : ℝ), Real.exp (-(t * s)) * binP2 s = muBin t / t := by
  have ht0 : t ≠ 0 := ht.ne'
  set I := ∫ s in Ioi (0 : ℝ), Real.exp (-(t * s)) * binP2 s with hI
  have hsplit : I = (∫ s in Ioc (0 : ℝ) 1, Real.exp (-(t * s)) * binP2 s) +
      ∫ s in Ioi (1 : ℝ), Real.exp (-(t * s)) * binP2 s := by
    rw [hI, ← Ioc_union_Ioi_eq_Ioi (zero_le_one' ℝ)]
    refine setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi ?_ ?_
    · exact (integrableOn_exp_mul_binP2 ht).mono_set (Ioc_subset_Ioi_self)
    · exact (integrableOn_exp_mul_binP2 ht).mono_set (Ioi_subset_Ioi zero_le_one)
  rw [integral_Ioi_one_shift t, integral_unit_period ht] at hsplit
  have hmu : muBin t = t⁻¹ * ((Real.exp t - 1)⁻¹ - t⁻¹ + 1 / 2) := by
    simp [muBin, ht0]
  have hX : Real.exp t - 1 ≠ 0 := (sub_pos.mpr (Real.one_lt_exp_iff.mpr ht)).ne'
  have hE : Real.exp (-t) = (Real.exp t)⁻¹ := Real.exp_neg t
  have hXpos : Real.exp t ≠ 0 := (Real.exp_pos t).ne'
  rw [hmu]
  have h1 : (1 - Real.exp (-t)) * I = Real.exp (-t) * (1 / t ^ 3 - 1 / (2 * t ^ 2) +
      (1 / t ^ 2 - 1 / (2 * t)) + 1 / (2 * t)) - (1 / t ^ 3 - 1 / (2 * t ^ 2)) := by
    linarith [hsplit]
  have hne : 1 - Real.exp (-t) ≠ 0 := by
    have : Real.exp (-t) < 1 := (Real.exp_lt_one_iff.mpr (by linarith))
    linarith
  apply mul_left_cancel₀ hne
  rw [h1, hE]
  field_simp
  ring

/-- info: 'FormalResearch.SignUncertainty.BinetDecay.laplace_binP2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms laplace_binP2

end FormalResearch.SignUncertainty.BinetDecay
