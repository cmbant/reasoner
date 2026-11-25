module

public import FormalResearch.SignUncertainty.CtOuterMittag
public import FormalResearch.SignUncertainty.CtOuterAltHarm
public import FormalResearch.SignUncertainty.CtOuterRatInt
public import FormalResearch.SignUncertainty.CtOuterDefs

/-!
# `∫_0^∞ t m'(t)/(1+t²) dt = π(1 - log 2)` (Mittag-Leffler and dominated convergence)

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, proof of `ct:outer` (2) ("Evaluation of `a_{1t2}`").
**Proved.**  With `t m'(t) = ∑ (-1)^n 2t²/((n+1)²+t²)` (`hasSum_mPrime`) the alternating partial sums are
bounded by `4` (`alternating_series_error_bound`), and `∫_0^∞ 2t²/((1+t²)((n+1)²+t²)) dt = π/(n+2)`
(`integral_rat'`); dominated convergence and `∑ (-1)^n/(n+2) = 1 - log 2` give the value.
-/

@[expose] public section

open Set Filter Topology MeasureTheory Finset
open scoped Real

namespace FormalResearch.SignUncertainty.CtOuter

/-- The terms `2t²/((n+1)²+t²)`. -/
noncomputable def altTerm (t : ℝ) (n : ℕ) : ℝ := 2 * t ^ 2 / (((n : ℝ) + 1) ^ 2 + t ^ 2)

lemma altTerm_nonneg (t : ℝ) (n : ℕ) : 0 ≤ altTerm t n := by unfold altTerm; positivity

lemma altTerm_antitone (t : ℝ) : Antitone (altTerm t) := by
  intro a b hab
  unfold altTerm
  have : (a : ℝ) ≤ b := by exact_mod_cast hab
  have h1 : 0 < ((a : ℝ) + 1) ^ 2 + t ^ 2 := by positivity
  rw [div_le_div_iff₀ (by positivity) h1]
  have : ((a : ℝ) + 1) ^ 2 ≤ ((b : ℝ) + 1) ^ 2 := by nlinarith [(Nat.cast_nonneg a : (0 : ℝ) ≤ a)]
  nlinarith [sq_nonneg t]

lemma altTerm_le_two (t : ℝ) (n : ℕ) : altTerm t n ≤ 2 := by
  unfold altTerm
  have h1 : 0 < ((n : ℝ) + 1) ^ 2 + t ^ 2 := by positivity
  rw [div_le_iff₀ h1]
  nlinarith [sq_nonneg ((n : ℝ) + 1), (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

lemma summable_altTerm (t : ℝ) : Summable (altTerm t) := by
  have hs : Summable (fun n : ℕ => 2 * t ^ 2 * (1 / ((n : ℝ) + 1) ^ 2)) := by
    have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
    simpa using this.mul_left (2 * t ^ 2)
  refine Summable.of_nonneg_of_le (altTerm_nonneg t) (fun n => ?_) hs
  unfold altTerm
  have h1 : 0 < ((n : ℝ) + 1) ^ 2 := by positivity
  rw [mul_one_div]
  exact div_le_div_of_nonneg_left (by positivity) h1 (by linarith [sq_nonneg t])

lemma hasSum_t_mPrime {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ => (-1 : ℝ) ^ n * altTerm t n) (t * mPrime t) := by
  have h := (FormalResearch.SignUncertainty.hasSum_mPrime ht).mul_left t
  have e : (fun n : ℕ => (-1 : ℝ) ^ n * altTerm t n) =
      fun n : ℕ => t * (2 * (-1 : ℝ) ^ n * t / (((n : ℝ) + 1) ^ 2 + t ^ 2)) := by
    funext n; unfold altTerm; ring
  rw [e]; exact h

/-- Alternating partial sums are bounded by `4`. -/
lemma abs_partial_le (t : ℝ) (N : ℕ) :
    |∑ i ∈ range N, (-1 : ℝ) ^ i * altTerm t i| ≤ 4 := by
  have hs := summable_altTerm t
  have hb := alternating_series_error_bound (altTerm t) (altTerm_antitone t) hs
  have h0 := hb 0
  have hN := hb N
  simp only [range_zero, sum_empty, sub_zero] at h0
  have := altTerm_le_two t 0
  have h3 := altTerm_le_two t N
  have := abs_sub_abs_le_abs_sub (∑ i ∈ range N, (-1 : ℝ) ^ i * altTerm t i) (∑' i : ℕ, (-1 : ℝ) ^ i * altTerm t i)
  have h4 := abs_sub_comm (∑' i : ℕ, (-1 : ℝ) ^ i * altTerm t i) (∑ i ∈ range N, (-1 : ℝ) ^ i * altTerm t i)
  linarith [abs_nonneg (∑' i : ℕ, (-1 : ℝ) ^ i * altTerm t i)]

lemma integral_partial (N : ℕ) :
    ∫ t in Ioi (0 : ℝ), (∑ i ∈ range N, (-1 : ℝ) ^ i * altTerm t i) / (1 + t ^ 2) =
      π * ∑ i ∈ range N, (-1 : ℝ) ^ i / ((i : ℝ) + 2) := by
  have hpt : ∀ t : ℝ, (∑ i ∈ range N, (-1 : ℝ) ^ i * altTerm t i) / (1 + t ^ 2) =
      ∑ i ∈ range N, (-1 : ℝ) ^ i * 2 * (t ^ 2 / ((1 + t ^ 2) * (((i : ℝ) + 1) ^ 2 + t ^ 2))) := by
    intro t
    rw [Finset.sum_div]
    refine sum_congr rfl (fun i _ => ?_)
    have h1 : (1 + t ^ 2) ≠ 0 := by positivity
    have h2 : ((i : ℝ) + 1) ^ 2 + t ^ 2 ≠ 0 := by positivity
    unfold altTerm
    field_simp
  simp_rw [hpt]
  rw [integral_finsetSum]
  · rw [Finset.mul_sum]
    refine sum_congr rfl (fun i _ => ?_)
    rw [integral_const_mul, integral_rat' (m := (i : ℝ) + 1) (by linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)])]
    have : ((i : ℝ) + 1 + 1) ≠ 0 := by positivity
    have h2 : ((i : ℝ) + 2) ≠ 0 := by positivity
    field_simp
    ring
  · intro i _
    exact (integrableOn_rat (m := (i : ℝ) + 1)
      (by linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)])).const_mul _

/-- **`∫_0^∞ t m'(t)/(1+t²) dt = π (1 - log 2)`.** -/
theorem integral_t_mPrime_div :
    ∫ t in Ioi (0 : ℝ), t * mPrime t / (1 + t ^ 2) = π * (1 - Real.log 2) := by
  set F : ℕ → ℝ → ℝ := fun N t => (∑ i ∈ range N, (-1 : ℝ) ^ i * altTerm t i) / (1 + t ^ 2) with hF
  have hlim : Tendsto (fun N : ℕ => ∫ t in Ioi (0 : ℝ), F N t) atTop
      (𝓝 (∫ t in Ioi (0 : ℝ), t * mPrime t / (1 + t ^ 2))) := by
    refine tendsto_integral_of_dominated_convergence (fun t => 4 * (1 / (1 + t ^ 2))) ?_ ?_ ?_ ?_
    · intro N
      refine Continuous.aestronglyMeasurable ?_
      simp only [hF]
      refine Continuous.div (continuous_finsetSum _ (fun i _ => ?_)) (by fun_prop) (fun t => by positivity)
      unfold altTerm
      exact continuous_const.mul (Continuous.div (by fun_prop) (by fun_prop) (fun t => by positivity))
    · exact integrableOn_inv_one_add_sq.const_mul 4
    · intro N
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 < t := ht
      simp only [hF]
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 1 + t ^ 2)]
      rw [mul_one_div]
      exact div_le_div_of_nonneg_right (abs_partial_le t N) (by positivity)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 < t := ht
      simp only [hF]
      exact ((hasSum_t_mPrime ht0).tendsto_sum_nat).div_const _
  have h2 : Tendsto (fun N : ℕ => ∫ t in Ioi (0 : ℝ), F N t) atTop (𝓝 (π * (1 - Real.log 2))) := by
    have : (fun N : ℕ => ∫ t in Ioi (0 : ℝ), F N t) =
        fun N : ℕ => π * ∑ i ∈ range N, (-1 : ℝ) ^ i / ((i : ℝ) + 2) := by
      funext N; exact integral_partial N
    rw [this]
    exact (FormalResearch.SignUncertainty.tendsto_altHarm).const_mul π
  exact tendsto_nhds_unique hlim h2

/-- info: 'FormalResearch.SignUncertainty.CtOuter.integral_t_mPrime_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms integral_t_mPrime_div

end FormalResearch.SignUncertainty.CtOuter
