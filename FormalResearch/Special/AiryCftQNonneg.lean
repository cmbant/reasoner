module

public import FormalResearch.Special.AiryCftQNCQuad

/-!
# Theorem Q (4) for nonnegative terms: summability is automatic

If the terms `f(a_n)/Ai'(a_n)²` (resp. `f(z) D(z)/N'(z)²`, resp. `f(z)/K(z,z)`) are real and nonnegative, the limit form of
Theorem Q (`airyQ_tendsto`, `airyNC_tendsto`) already gives summability (the partial sums are monotone and converge along
the good circles), hence the `HasSum` identity `∫_ℝ f = Σ ...` for every `f ∈ 𝒢` with `f ∈ L¹(ℝ)`, **without** the sampling
bound of Theorem Q (3) (`airyQ_hasSum_of_nonneg`, `airyNC_hasSum_of_nonneg`).  This is the case used for the positivity
arguments (`f = |ψ|²`, `f ≥ 0` on the nodes).  All **proved**.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.Special

/-- **Theorem Q (4), nonnegative terms.**  If every term `f(a_n)/Ai'(a_n)²` is real and `≥ 0` (`f ∈ 𝒢`, `f ∈ L¹(ℝ)`, any
real `ν`), then the series converges and `∫_ℝ f = Σ_n f(a_n)/Ai'(a_n)²`. -/
theorem airyQ_hasSum_of_nonneg {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hfi : Integrable (fun x : ℝ => f (x : ℂ)))
    {C ν : ℝ} (hC : 0 ≤ C) (hb : ∀ u : ℂ, ‖f u‖ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u)
    (hn : ∀ n : ℕ, 0 ≤ (f (airyZero (n + 1) : ℂ) / (deriv airyAiC (airyZero (n + 1) : ℂ)) ^ 2).re ∧
      (f (airyZero (n + 1) : ℂ) / (deriv airyAiC (airyZero (n + 1) : ℂ)) ^ 2).im = 0) :
    HasSum (fun n : ℕ => f (airyZero (n + 1) : ℂ) / (deriv airyAiC (airyZero (n + 1) : ℂ)) ^ 2)
      (∫ x : ℝ, f (x : ℂ)) := by
  set u : ℕ → ℂ := fun n => f (airyZero (n + 1) : ℂ) / (deriv airyAiC (airyZero (n + 1) : ℂ)) ^ 2 with hu
  obtain ⟨N, hN, ht⟩ := airyQ_tendsto hf hfi hC hb
  have ht' : Tendsto (fun k => ∑ j ∈ Finset.range (N k), u j) atTop (𝓝 (∫ x : ℝ, f (x : ℂ))) :=
    ht.congr fun k => airyCft_sum_Icc (fun n : ℕ => f (airyZero n : ℂ) / (deriv airyAiC (airyZero n : ℂ)) ^ 2) (N k)
  have hre : Tendsto (fun k => ∑ j ∈ Finset.range (N k), (u j).re) atTop (𝓝 ((∫ x : ℝ, f (x : ℂ)).re)) := by
    have := (Complex.continuous_re.tendsto _).comp ht'
    refine this.congr fun k => ?_
    simp [Function.comp, Complex.re_sum, hu]
  have hsum : Summable (fun n => (u n).re) := by
    refine summable_of_sum_range_le (fun n => (hn n).1) (c := (∫ x : ℝ, f (x : ℂ)).re) fun m => ?_
    refine ge_of_tendsto hre ?_
    filter_upwards [hN.eventually_ge_atTop m] with k hk
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hk) fun j _ _ => (hn j).1
  have hs : Summable u := by
    have : u = fun n => (((u n).re : ℝ) : ℂ) := by
      funext n; exact Complex.ext (by simp) (by simp; exact (hn n).2)
    rw [this]
    exact Complex.summable_ofReal.mpr hsum
  exact airyQ_hasSum hf hfi hC hb hs

/-- **Theorem Q (4) for `N = P Ai + Q Ai'`, nonnegative terms.** -/
theorem airyNC_hasSum_of_nonneg (P Q : ℝ) (hQ : Q ≠ 0) {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hfi : Integrable (fun x : ℝ => f (x : ℂ))) {C ν : ℝ} (hC : 0 ≤ C)
    (hb : ∀ u : ℂ, ‖f u‖ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u)
    (hn : ∀ z : {z : ℂ // airyNC P Q z = 0},
      0 ≤ (f z * (airyDC P Q z / airyNC' P Q z ^ 2)).re ∧ (f z * (airyDC P Q z / airyNC' P Q z ^ 2)).im = 0) :
    HasSum (fun z : {z : ℂ // airyNC P Q z = 0} => f z * (airyDC P Q z / airyNC' P Q z ^ 2))
      (∫ x : ℝ, f (x : ℂ)) := by
  set u : {z : ℂ // airyNC P Q z = 0} → ℂ := fun z => f z * (airyDC P Q z / airyNC' P Q z ^ 2) with hu
  obtain ⟨T, hT, ht⟩ := airyNC_tendsto P Q hQ hf hfi hC hb
  have hre : Tendsto (fun k => ∑ z ∈ T k, (u z).re) atTop (𝓝 ((∫ x : ℝ, f (x : ℂ)).re)) := by
    have := (Complex.continuous_re.tendsto _).comp ht
    refine this.congr fun k => ?_
    simp [Function.comp, Complex.re_sum, hu]
  have hsum : Summable (fun z => (u z).re) := by
    refine summable_of_sum_le (fun z => (hn z).1) (c := (∫ x : ℝ, f (x : ℂ)).re) fun s => ?_
    refine ge_of_tendsto hre ?_
    filter_upwards [hT.eventually_ge_atTop s] with k hk
    exact Finset.sum_le_sum_of_subset_of_nonneg hk fun j _ _ => (hn j).1
  have hs : Summable u := by
    have : u = fun z => (((u z).re : ℝ) : ℂ) := by
      funext z; exact Complex.ext (by simp) (by simp; exact (hn z).2)
    rw [this]
    exact Complex.summable_ofReal.mpr hsum
  exact airyNC_hasSum P Q hQ hf hfi hC hb hs

/-- info: 'FormalResearch.Special.airyQ_hasSum_of_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyQ_hasSum_of_nonneg

/-- info: 'FormalResearch.Special.airyNC_hasSum_of_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyNC_hasSum_of_nonneg

end FormalResearch.Special
