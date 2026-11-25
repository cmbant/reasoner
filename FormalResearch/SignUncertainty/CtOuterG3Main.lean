module

public import FormalResearch.SignUncertainty.CtOuterG3Rat
public import FormalResearch.SignUncertainty.CtOuterG3Zeta
public import FormalResearch.SignUncertainty.CtOuterK
public import FormalResearch.SignUncertainty.CtOuterC3

/-!
# `c_{3,1t2} = ½ζ(3) - 1/3`

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, `ct:outer` (2) (the `-½ log(1+t²)` summand of `c_{3,h}`).
**Proved**: `∫_0^∞ g(t) cosh(πt)/sinh²(πt) dt = (3ζ(3)/2 - 1)/π` with `g = 1 - (1-t²)/(1+t²)²`, by integration
by parts to `(1/π) ∫ g'(t)/sinh(πt) dt`, the Mittag-Leffler series (`hasSum_mPrime`), dominated convergence and the
rational integrals `integral_rP`, and `∑_{k≥2} (-1)^k/k³ = 1 - ¾ζ(3)`.
-/

@[expose] public section

open Set Filter Topology MeasureTheory Finset
open scoped Real

namespace FormalResearch.SignUncertainty.CtOuter

/-- `g'(t) = t · r(t) = (6t - 2t³)/(1+t²)³`. -/
noncomputable def gd (t : ℝ) : ℝ := t * rG t

lemma t_mPrime_eq {t : ℝ} (ht : 0 < t) : t * mPrime t = 1 - π * t / Real.sinh (π * t) := by
  unfold mPrime
  have hs : Real.sinh (π * t) ≠ 0 := (Real.sinh_pos_iff.mpr (by positivity)).ne'
  field_simp

lemma t_mPrime_mem {t : ℝ} (ht : 0 < t) : 0 ≤ t * mPrime t ∧ t * mPrime t ≤ 1 := by
  rw [t_mPrime_eq ht]
  have hs : 0 < Real.sinh (π * t) := Real.sinh_pos_iff.mpr (by positivity)
  have h1 : π * t ≤ Real.sinh (π * t) := Real.self_le_sinh_iff.mpr (by positivity)
  have h2 : π * t / Real.sinh (π * t) ≤ 1 := (div_le_one hs).2 h1
  have h3 : 0 < π * t / Real.sinh (π * t) := by positivity
  constructor <;> linarith only [h2, h3]

lemma continuousOn_mPrime : ContinuousOn mPrime (Ioi 0) := fun _ ht =>
  (hasDerivAt_mPrime ht).continuousAt.continuousWithinAt

lemma continuous_rG : Continuous rG := by
  unfold rG
  exact Continuous.div (by fun_prop) (by fun_prop) (fun t => by positivity)

lemma integrableOn_rG_t_mPrime : IntegrableOn (fun t : ℝ => rG t * (t * mPrime t)) (Ioi 0) := by
  have h := integrableOn_rG.norm
  refine Integrable.mono' h ?_ ?_
  · exact (continuous_rG.continuousOn.mul (continuousOn_id.mul continuousOn_mPrime)).aestronglyMeasurable
      measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hm := t_mPrime_mem (show 0 < t from ht)
    rw [norm_mul, Real.norm_of_nonneg hm.1]
    calc ‖rG t‖ * (t * mPrime t) ≤ ‖rG t‖ * 1 := mul_le_mul_of_nonneg_left hm.2 (norm_nonneg _)
      _ = ‖rG t‖ := mul_one _

/-- **`∫_0^∞ r(t) · t m'(t) dt = 2π (1 - ¾ζ(3))`** (Mittag-Leffler series + dominated convergence). -/
theorem integral_rG_t_mPrime :
    ∫ t in Ioi (0 : ℝ), rG t * (t * mPrime t) = 2 * π * (1 - 3 / 4 * (riemannZeta 3).re) := by
  set F : ℕ → ℝ → ℝ := fun N t => rG t * ∑ i ∈ range N, (-1 : ℝ) ^ i * altTerm t i with hF
  have hlim : Tendsto (fun N : ℕ => ∫ t in Ioi (0 : ℝ), F N t) atTop
      (𝓝 (∫ t in Ioi (0 : ℝ), rG t * (t * mPrime t))) := by
    refine tendsto_integral_of_dominated_convergence (fun t => 4 * |rG t|) ?_ ?_ ?_ ?_
    · intro N
      refine Continuous.aestronglyMeasurable ?_
      simp only [hF]
      refine continuous_rG.mul (continuous_finsetSum _ (fun i _ => ?_))
      unfold altTerm
      exact continuous_const.mul (Continuous.div (by fun_prop) (by fun_prop) (fun t => by positivity))
    · exact integrableOn_rG.norm.const_mul 4
    · intro N
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t _
      simp only [hF]
      rw [Real.norm_eq_abs, abs_mul]
      calc |rG t| * |∑ i ∈ range N, (-1 : ℝ) ^ i * altTerm t i| ≤ |rG t| * 4 :=
            mul_le_mul_of_nonneg_left (abs_partial_le t N) (abs_nonneg _)
        _ = 4 * |rG t| := by ring
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 < t := ht
      simp only [hF]
      exact ((hasSum_t_mPrime ht0).tendsto_sum_nat).const_mul _
  have h2 : Tendsto (fun N : ℕ => ∫ t in Ioi (0 : ℝ), F N t) atTop
      (𝓝 (2 * π * (1 - 3 / 4 * (riemannZeta 3).re))) := by
    have hI : ∀ N : ℕ, ∫ t in Ioi (0 : ℝ), F N t =
        2 * π * ∑ i ∈ range N, (-1 : ℝ) ^ i / ((i : ℝ) + 2) ^ 3 := by
      intro N
      have hpt : ∀ t : ℝ, F N t = ∑ i ∈ range N, (-1 : ℝ) ^ i * rP ((i : ℝ) + 1) t := by
        intro t
        simp only [hF, rP, altTerm]
        rw [Finset.mul_sum]
        refine sum_congr rfl (fun i _ => ?_)
        ring
      simp_rw [hpt]
      rw [integral_finsetSum, Finset.mul_sum]
      · refine sum_congr rfl (fun i _ => ?_)
        rw [integral_const_mul, integral_rP (by linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)])]
        have : ((i : ℝ) + 1 + 1) = (i : ℝ) + 2 := by ring
        rw [this]
        ring
      · intro i _
        exact (integrableOn_rP (by linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)])).const_mul _
    simp_rw [hI]
    exact tendsto_alt_zeta3.const_mul _
  exact tendsto_nhds_unique hlim h2

lemma gd_div_sinh_eq {t : ℝ} (ht : 0 < t) :
    gd t / Real.sinh (π * t) = (1 / π) * (rG t - rG t * (t * mPrime t)) := by
  unfold gd
  rw [t_mPrime_eq ht]
  have hs : Real.sinh (π * t) ≠ 0 := (Real.sinh_pos_iff.mpr (by positivity)).ne'
  have hpi := Real.pi_pos.ne'
  field_simp
  ring

lemma integrableOn_gd_div_sinh : IntegrableOn (fun t : ℝ => gd t / Real.sinh (π * t)) (Ioi 0) := by
  have h := (integrableOn_rG.sub integrableOn_rG_t_mPrime).const_mul (1 / π)
  exact IntegrableOn.congr_fun h (fun t ht => by simp only [Pi.sub_apply]; exact (gd_div_sinh_eq ht).symm)
    measurableSet_Ioi

/-- **`∫_0^∞ g'(t)/sinh(πt) dt = (3/2)ζ(3) - 1`.** -/
theorem integral_gd_div_sinh :
    ∫ t in Ioi (0 : ℝ), gd t / Real.sinh (π * t) = 3 / 2 * (riemannZeta 3).re - 1 := by
  have h : ∫ t in Ioi (0 : ℝ), gd t / Real.sinh (π * t) =
      ∫ t in Ioi (0 : ℝ), (1 / π) * (rG t - rG t * (t * mPrime t)) :=
    setIntegral_congr_fun measurableSet_Ioi (fun t ht => gd_div_sinh_eq ht)
  rw [h, integral_const_mul, integral_sub integrableOn_rG integrableOn_rG_t_mPrime, integral_rG,
    integral_rG_t_mPrime]
  have := Real.pi_pos.ne'
  field_simp
  ring

/-- info: 'FormalResearch.SignUncertainty.CtOuter.integral_rG_t_mPrime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms integral_rG_t_mPrime

/-- info: 'FormalResearch.SignUncertainty.CtOuter.integral_gd_div_sinh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms integral_gd_div_sinh

end FormalResearch.SignUncertainty.CtOuter
