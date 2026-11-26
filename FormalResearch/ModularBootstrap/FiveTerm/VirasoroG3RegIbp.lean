module

public import FormalResearch.ModularBootstrap.FiveTerm.VirasoroG3Poisson
public import FormalResearch.ModularBootstrap.FiveTerm.VirasoroG3Elem1

/-!
# Regularised integration by parts for the quotient amplitude (FIVE-0b)

For an even amplitude `a` and `b = (a - a(0))/sinh²(πt)`, the slope of `b` is
`∫_ℝ (b - b(0)) π cosh/sinh² = lim_{δ → 0⁺} 2 [(1/3)∫_δ^∞ a'/sinh³ + (b(δ)/3 - b(0))/sinh(πδ)]`.  Proved.
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real
open FormalResearch.ModularBootstrap.FiveTerm.StripOuter

namespace FormalResearch.ModularBootstrap.FiveTerm

lemma hasDerivAt_neg_inv_sinh_cube {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun x : ℝ => -(3 * π * Real.sinh (π * x) ^ 3)⁻¹)
      (Real.cosh (π * x) / Real.sinh (π * x) ^ 4) x := by
  have hpi := Real.pi_pos
  have hs := sinh_pos_of_pos hx
  have h1 : HasDerivAt (fun x : ℝ => 3 * π * Real.sinh (π * x) ^ 3)
      (3 * π * (3 * Real.sinh (π * x) ^ 2 * (π * Real.cosh (π * x)))) x := by
    have := ((hd_sinh1 x).pow 3).const_mul (3 * π)
    simpa using this
  have h2 := (h1.inv (by positivity)).neg
  refine h2.congr_deriv ?_
  field_simp

lemma sinh_mono_of_le {s t : ℝ} (h : s ≤ t) : Real.sinh (π * s) ≤ Real.sinh (π * t) :=
  Real.sinh_le_sinh.mpr (mul_le_mul_of_nonneg_left h Real.pi_pos.le)

/-- The regularised integration by parts. -/
theorem reg_ibp {a a' b : ℝ → ℝ} (ha : Amp a) (hd : ∀ t : ℝ, 0 < t → HasDerivAt a (a' t) t)
    (hab : ∀ t : ℝ, t ≠ 0 → b t = (a t - a 0) / Real.sinh (π * t) ^ 2)
    (hint : ∀ δ : ℝ, 0 < δ → IntegrableOn (fun t => a' t / Real.sinh (π * t) ^ 3) (Ioi δ))
    {δ : ℝ} (hδ : 0 < δ) :
    ∫ t in Ioi δ, (b t - b 0) * (π * kern t) =
      (1 / 3) * (∫ t in Ioi δ, a' t / Real.sinh (π * t) ^ 3) + (b δ / 3 - b 0) / Real.sinh (π * δ) := by
  have hpi := Real.pi_pos
  obtain ⟨Cb, hCb⟩ := slope_bound ha
  obtain ⟨M, hM⟩ := ha.bdd
  have hsδ := sinh_pos_of_pos hδ
  set u : ℝ → ℝ := fun t => a t - a 0 with hu
  set v : ℝ → ℝ := fun t => -(3 * π * Real.sinh (π * t) ^ 3)⁻¹ with hv
  have hu' : ∀ x ∈ Ioi δ, HasDerivAt u (a' x) x := fun x hx => (hd x (lt_trans hδ hx)).sub_const _
  have hv' : ∀ x ∈ Ioi δ, HasDerivAt v (Real.cosh (π * x) / Real.sinh (π * x) ^ 4) x :=
    fun x hx => hasDerivAt_neg_inv_sinh_cube (lt_trans hδ hx)
  -- integrability of u v'
  have huv' : IntegrableOn (u * fun x => Real.cosh (π * x) / Real.sinh (π * x) ^ 4) (Ioi δ) := by
    have hcont : ContinuousOn (u * fun x => Real.cosh (π * x) / Real.sinh (π * x) ^ 4) (Ioi δ) := by
      refine ((ha.cont.sub continuous_const).continuousOn).mul ?_
      refine (Real.continuous_cosh.comp (continuous_const.mul continuous_id)).continuousOn.div
        ((Real.continuous_sinh.comp (continuous_const.mul continuous_id)).pow 4).continuousOn ?_
      intro t ht
      have := sinh_pos_of_pos (lt_trans hδ ht)
      positivity
    refine Integrable.mono' (((integrable_exp_neg_mul_abs one_pos).const_mul
      (Cb / (π * Real.sinh (π * δ) ^ 2))).integrableOn) (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    have htδ : δ < t := ht
    have ht0 : 0 < t := lt_trans hδ htδ
    have hst := sinh_pos_of_pos ht0
    have hmono : Real.sinh (π * δ) ≤ Real.sinh (π * t) := sinh_mono_of_le htδ.le
    have hb := hCb t ht0.ne'
    simp only [Pi.mul_apply, hu, Real.norm_eq_abs]
    have hnn : 0 ≤ Real.cosh (π * t) / Real.sinh (π * t) ^ 4 := by
      have := Real.cosh_pos (π * t); positivity
    have key : |a t - a 0| * (Real.cosh (π * t) / Real.sinh (π * t) ^ 4) =
        (|a t - a 0| * (π * kern t)) * (1 / (π * Real.sinh (π * t) ^ 2)) := by
      unfold kern; field_simp
    rw [abs_mul, abs_of_nonneg hnn, key]
    have h2 : 1 / (π * Real.sinh (π * t) ^ 2) ≤ 1 / (π * Real.sinh (π * δ) ^ 2) := by
      apply one_div_le_one_div_of_le (by positivity)
      have := pow_le_pow_left₀ hsδ.le hmono 2
      nlinarith only [this, hpi]
    have hCbe : 0 ≤ Cb * Real.exp (-(1 * |t|)) := (mul_nonneg (abs_nonneg _) (by
      have := kern_nonneg t; positivity)).trans hb
    calc |a t - a 0| * (π * kern t) * (1 / (π * Real.sinh (π * t) ^ 2))
        ≤ (Cb * Real.exp (-(1 * |t|))) * (1 / (π * Real.sinh (π * δ) ^ 2)) :=
          mul_le_mul hb h2 (by positivity) hCbe
      _ = Cb / (π * Real.sinh (π * δ) ^ 2) * Real.exp (-(1 * |t|)) := by ring
  -- integrability of u' v
  have hu'v : IntegrableOn (a' * v) (Ioi δ) := by
    refine ((hint δ hδ).const_mul (-(1 / (3 * π)))).congr ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    have := sinh_pos_of_pos (lt_trans hδ ht)
    simp only [Pi.mul_apply, hv]
    field_simp
  -- boundary terms
  have hz : Tendsto (u * v) (𝓝[>] δ) (𝓝 (u δ * v δ)) := by
    have hc : ContinuousAt (u * v) δ := by
      have h1 : ContinuousAt u δ := (ha.cont.sub continuous_const).continuousAt
      have h2 : ContinuousAt v δ := (hasDerivAt_neg_inv_sinh_cube hδ).continuousAt
      exact h1.mul h2
    exact hc.tendsto.mono_left nhdsWithin_le_nhds
  have hinf : Tendsto (u * v) atTop (𝓝 0) := by
    have hexp : Tendsto (fun t : ℝ => 64 * (|M| + |a 0|) / (3 * π) * Real.exp ((1 - 3 * π) * t)) atTop (𝓝 0) := by
      have : Tendsto (fun t : ℝ => Real.exp ((1 - 3 * π) * t)) atTop (𝓝 0) :=
        Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by linarith [Real.pi_gt_three]))
      simpa using this.const_mul (64 * (|M| + |a 0|) / (3 * π))
    refine squeeze_zero_norm' ?_ hexp
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with t ht
    have ht0 : 0 < t := by linarith
    have hex1 : 1 ≤ Real.exp t := Real.one_le_exp ht0.le
    have h1 : |a t - a 0| ≤ (|M| + |a 0|) * Real.exp t := by
      have := hM t
      rw [abs_of_pos ht0] at this
      have h2 : M * Real.exp t ≤ |M| * Real.exp t :=
        mul_le_mul_of_nonneg_right (le_abs_self M) (Real.exp_pos _).le
      calc |a t - a 0| ≤ |a t| + |a 0| := abs_sub _ _
        _ ≤ |M| * Real.exp t + |a 0| * 1 := by linarith
        _ ≤ |M| * Real.exp t + |a 0| * Real.exp t := by nlinarith [abs_nonneg (a 0)]
        _ = _ := by ring
    have hs1 : Real.exp (π * t) / 4 ≤ Real.sinh (π * t) := sinh_ge_exp (by nlinarith [Real.pi_gt_three])
    have hspos := sinh_pos_of_pos ht0
    have hs3 : Real.exp (π * t) ^ 3 / 64 ≤ Real.sinh (π * t) ^ 3 := by
      have := pow_le_pow_left₀ (by positivity) hs1 3
      calc Real.exp (π * t) ^ 3 / 64 = (Real.exp (π * t) / 4) ^ 3 := by ring
        _ ≤ _ := this
    simp only [Pi.mul_apply, hu, hv, Real.norm_eq_abs, abs_mul, abs_neg]
    rw [abs_of_pos (show 0 < (3 * π * Real.sinh (π * t) ^ 3)⁻¹ by positivity)]
    have hE : Real.exp (π * t) ^ 3 = Real.exp (3 * π * t) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    have hE2 : Real.exp t * Real.exp (-(3 * π * t)) = Real.exp ((1 - 3 * π) * t) := by
      rw [← Real.exp_add]; congr 1; ring
    have hinv : (3 * π * Real.sinh (π * t) ^ 3)⁻¹ ≤ 64 / (3 * π) * Real.exp (-(3 * π * t)) := by
      rw [inv_eq_one_div, div_le_iff₀ (by positivity)]
      have : Real.exp (3 * π * t) * Real.exp (-(3 * π * t)) = 1 := by rw [← Real.exp_add]; simp
      have hh : 0 < Real.exp (-(3 * π * t)) := Real.exp_pos _
      rw [hE] at hs3
      have e1 : 64 / (3 * π) * Real.exp (-(3 * π * t)) * (3 * π * Real.sinh (π * t) ^ 3) =
          64 * Real.exp (-(3 * π * t)) * Real.sinh (π * t) ^ 3 := by field_simp
      rw [e1]
      have := mul_le_mul_of_nonneg_left hs3 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 64) hh.le)
      nlinarith only [this, ‹Real.exp (3 * π * t) * Real.exp (-(3 * π * t)) = 1›]
    calc |a t - a 0| * (3 * π * Real.sinh (π * t) ^ 3)⁻¹
        ≤ ((|M| + |a 0|) * Real.exp t) * (64 / (3 * π) * Real.exp (-(3 * π * t))) :=
          mul_le_mul h1 hinv (by positivity) (by positivity)
      _ = 64 * (|M| + |a 0|) / (3 * π) * Real.exp ((1 - 3 * π) * t) := by
          rw [← hE2]; ring
  -- apply the integration by parts
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul hu' hv' huv' hu'v hz hinf
  obtain ⟨hkI, hkv⟩ := int_kern hδ
  -- rewrite the integrand
  have hrw : ∀ t ∈ Ioi δ, (b t - b 0) * (π * kern t) =
      π * (u t * (Real.cosh (π * t) / Real.sinh (π * t) ^ 4)) - b 0 * (π * kern t) := by
    intro t ht
    have ht0 : 0 < t := lt_trans hδ ht
    have hst := sinh_pos_of_pos ht0
    rw [hab t ht0.ne']
    simp only [hu]
    unfold kern
    field_simp
  set J : ℝ := ∫ t in Ioi δ, a' t / Real.sinh (π * t) ^ 3 with hJ
  rw [setIntegral_congr_fun measurableSet_Ioi hrw]
  have hI1 : IntegrableOn (fun t => π * (u t * (Real.cosh (π * t) / Real.sinh (π * t) ^ 4))) (Ioi δ) :=
    huv'.const_mul π
  have hI2 : IntegrableOn (fun t => b 0 * (π * kern t)) (Ioi δ) := (hkI.const_mul π).const_mul (b 0)
  rw [integral_sub hI1 hI2, integral_const_mul, integral_const_mul, integral_const_mul, hkv]
  have hu'v_int : ∫ x in Ioi δ, a' x * v x = -(1 / (3 * π)) * J := by
    rw [hJ, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have := sinh_pos_of_pos (lt_trans hδ ht)
    simp only [hv]
    field_simp
  have hmul : ∫ x in Ioi δ, u x * (Real.cosh (π * x) / Real.sinh (π * x) ^ 4) =
      ∫ x in Ioi δ, (u * fun x => Real.cosh (π * x) / Real.sinh (π * x) ^ 4) x := rfl
  rw [hmul]
  have hibp' : ∫ x in Ioi δ, (u * fun x => Real.cosh (π * x) / Real.sinh (π * x) ^ 4) x =
      0 - u δ * v δ - ∫ x in Ioi δ, (a' * v) x := hibp
  rw [hibp']
  have hpv : ∫ x in Ioi δ, (a' * v) x = ∫ x in Ioi δ, a' x * v x := rfl
  rw [hpv, hu'v_int]
  have hbδ := hab δ hδ.ne'
  simp only [hu, hv, QC]
  rw [hbδ]
  field_simp
  ring

end FormalResearch.ModularBootstrap.FiveTerm
