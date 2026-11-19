/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff

/-!
# Continuity in a parameter

Tools for continuity in a parameter: Cauchy's formula for the difference quotient `dslope` of an
entire function and its joint continuity in a parameter, local uniform convergence from joint
continuity, and continuity of series that are locally dominated from some index on.

## Main results

* `dslope_eq_circleIntegral`, `continuousOn_dslope_param`: the difference quotient of a family of
  entire functions as a circle integral, jointly continuous in the parameter and the point.
* `tendstoUniformlyOnFilter_of_continuousAt`: joint continuity at `(b, x)` gives uniform
  convergence near `x` as the parameter tends to `b`.
* `continuous_tsum_of_eventually_dominated`, `analyticOnNhd_tsum_of_eventually_dominated`: a
  series of continuous (entire) functions, locally dominated from some index on, has a continuous
  (entire) sum.
-/

@[expose] public section

open Complex Filter Set Metric
open scoped Real Topology

noncomputable section

/-- Cauchy's formula for the difference quotient of an entire function. -/
theorem dslope_eq_circleIntegral {f : ℂ → ℂ} (hf : Differentiable ℂ f) (n : ℂ) {R : ℝ}
    {c : ℂ} (hc : c ∈ ball n R) :
    dslope f n c = (2 * π * I : ℂ)⁻¹ • ∫ θ : ℝ in 0..2 * π,
      circleMap 0 R θ * I * ((circleMap n R θ - c)⁻¹ *
        ((f (circleMap n R θ) - f n) / (circleMap n R θ - n))) := by
  have hR : 0 < R := pos_of_mem_ball hc
  have hd : Differentiable ℂ (dslope f n) := by
    rw [← differentiableOn_univ, differentiableOn_dslope univ_mem]
    exact hf.differentiableOn
  rw [← (hd.diffContOnCl (s := ball n R)).two_pi_i_inv_smul_circleIntegral_sub_inv_smul hc]
  congr 1
  unfold circleIntegral
  refine intervalIntegral.integral_congr fun θ _ => ?_
  have hne : circleMap n R θ ≠ n := by
    intro h
    have := circleMap_sub_center n R θ
    rw [h, sub_self] at this
    exact (circleMap_ne_center hR.ne') h
  simp only [smul_eq_mul]
  rw [deriv_circleMap, dslope_of_ne _ hne, slope_def_field]

/-- The difference quotient of a family of entire functions depends continuously on the
parameter and the point. -/
theorem continuousOn_dslope_param {X : Type*} [TopologicalSpace X] {f : X → ℂ → ℂ} {s : Set X}
    (hs : IsOpen s) (hf : ContinuousOn (fun p : X × ℂ => f p.1 p.2) (s ×ˢ univ))
    (hd : ∀ x ∈ s, Differentiable ℂ (f x)) (n : ℂ) :
    ContinuousOn (fun p : X × ℂ => dslope (f p.1) n p.2) (s ×ˢ univ) := by
  rintro ⟨x₀, c₀⟩ ⟨hx₀, -⟩
  set R : ℝ := ‖c₀ - n‖ + 1 with hRdef
  have hR : 0 < R := by positivity
  set T : Set (X × ℂ) := s ×ˢ ball c₀ (1 / 2) with hT
  have hTo : IsOpen T := hs.prod isOpen_ball
  have hmem : (x₀, c₀) ∈ T := ⟨hx₀, mem_ball_self (by norm_num)⟩
  have hcball : ∀ p ∈ T, p.2 ∈ ball n R := by
    intro p hp
    have h1 := mem_ball.mp hp.2
    rw [mem_ball, dist_eq_norm] at *
    calc ‖p.2 - n‖ ≤ ‖p.2 - c₀‖ + ‖c₀ - n‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < R := by linarith
  set F : X × ℂ → ℝ → ℂ := fun p θ => circleMap 0 R θ * I * ((circleMap n R θ - p.2)⁻¹ *
      ((f p.1 (circleMap n R θ) - f p.1 n) / (circleMap n R θ - n))) with hF
  have heq : EqOn (fun p : X × ℂ => dslope (f p.1) n p.2)
      (fun p => (2 * π * I : ℂ)⁻¹ • ∫ θ : ℝ in 0..2 * π, F p θ) T := fun p hp =>
    dslope_eq_circleIntegral (hd p.1 hp.1) n (hcball p hp)
  have hcont : ContinuousOn (fun p => (2 * π * I : ℂ)⁻¹ • ∫ θ : ℝ in 0..2 * π, F p θ) T := by
    rw [continuousOn_iff_continuous_domRestrict]
    change Continuous fun q : T => (2 * π * I : ℂ)⁻¹ • ∫ θ : ℝ in 0..2 * π, F q.1 θ
    refine Continuous.smul (continuous_const (y := (2 * π * I : ℂ)⁻¹)) ?_
    refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' ?_ _ _
    have hfc : Continuous fun r : T × ℝ => f r.1.1.1 (circleMap n R r.2) := by
      refine hf.comp_continuous (f := fun r : T × ℝ => (r.1.1.1, circleMap n R r.2))
        (by fun_prop) fun r => ⟨r.1.2.1, mem_univ _⟩
    have hfn : Continuous fun r : T × ℝ => f r.1.1.1 n := by
      refine hf.comp_continuous (f := fun r : T × ℝ => (r.1.1.1, n))
        (by fun_prop) fun r => ⟨r.1.2.1, mem_univ _⟩
    have hne1 : ∀ r : T × ℝ, circleMap n R r.2 - r.1.1.2 ≠ 0 := by
      intro r h
      have h1 := hcball r.1.1 r.1.2
      rw [sub_eq_zero] at h
      rw [← h, mem_ball, dist_eq_norm, circleMap_sub_center, norm_circleMap_zero,
        abs_of_pos hR] at h1
      exact lt_irrefl _ h1
    have hne2 : ∀ r : T × ℝ, circleMap n R r.2 - n ≠ 0 := fun r =>
      sub_ne_zero.mpr (circleMap_ne_center hR.ne')
    simp only [hF]
    refine Continuous.mul (by fun_prop) (Continuous.mul ?_ ?_)
    · exact Continuous.inv₀ (by fun_prop) hne1
    · exact Continuous.div (hfc.sub hfn) (by fun_prop) hne2
  exact ((hcont.congr heq).continuousAt (hTo.mem_nhds hmem)).continuousWithinAt

/-- Joint continuity at `(b, x)` gives uniform convergence near `x` as the parameter tends
to `b`. -/
theorem tendstoUniformlyOnFilter_of_continuousAt {F : ℂ → ℂ → ℂ} {b x : ℂ}
    (h : ContinuousAt (fun p : ℂ × ℂ => F p.1 p.2) (b, x)) {l : Filter ℂ} (hl : l ≤ 𝓝 b) :
    TendstoUniformlyOnFilter F (F b) l (𝓝 x) := by
  rw [Metric.tendstoUniformlyOnFilter_iff]
  intro ε hε
  have h1 : ∀ᶠ p : ℂ × ℂ in 𝓝 (b, x), dist (F p.1 p.2) (F b x) < ε / 2 :=
    Metric.tendsto_nhds.mp h (ε / 2) (by positivity)
  have h2 : ∀ᶠ w in 𝓝 x, dist (F b w) (F b x) < ε / 2 := by
    have hc : ContinuousAt (fun w => F b w) x :=
      ContinuousAt.comp (f := fun w => (b, w)) h (by fun_prop)
    exact Metric.tendsto_nhds.mp hc (ε / 2) (by positivity)
  have h1' : ∀ᶠ p : ℂ × ℂ in l ×ˢ 𝓝 x, dist (F p.1 p.2) (F b x) < ε / 2 := by
    rw [nhds_prod_eq] at h1
    exact Filter.Eventually.filter_mono (Filter.prod_mono hl le_rfl) h1
  filter_upwards [h1', h2.prod_inr l] with p hp1 hp2
  calc dist (F b p.2) (F p.1 p.2) ≤ dist (F b p.2) (F b x) + dist (F p.1 p.2) (F b x) :=
        dist_triangle_right _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add hp2 hp1
    _ = ε := by ring

/-- A series of continuous functions whose terms are, near every point, eventually dominated
by a summable sequence has a continuous sum. -/
theorem continuous_tsum_of_eventually_dominated {X : Type*} [TopologicalSpace X]
    {F : ℕ → X → ℂ} (hF : ∀ n, Continuous (F n)) (hsum : ∀ x, Summable fun n => F n x)
    (hdom : ∀ x₀ : X, ∃ U : Set X, IsOpen U ∧ x₀ ∈ U ∧ ∃ N : ℕ, ∃ u : ℕ → ℝ, Summable u ∧
      ∀ n, N ≤ n → ∀ x ∈ U, ‖F n x‖ ≤ u n) :
    Continuous (fun x => ∑' n, F n x) := by
  refine continuous_iff_continuousAt.mpr fun x₀ => ?_
  obtain ⟨U, hU, hx₀, N, u, hu, hle⟩ := hdom x₀
  have htail : ContinuousOn (fun x => ∑' k, F (k + N) x) U :=
    continuousOn_tsum (u := fun k => u (k + N)) (fun k => (hF (k + N)).continuousOn)
      (hu.comp_injective (add_left_injective N)) (fun k x hx => hle (k + N) (by omega) x hx)
  have hfin : ContinuousOn (fun x => ∑ n ∈ Finset.range N, F n x) U :=
    continuousOn_finsetSum _ fun n _ => (hF n).continuousOn
  exact ((hfin.add htail).congr fun x _ => ((hsum x).sum_add_tsum_nat_add N).symm).continuousAt
    (hU.mem_nhds hx₀)

/-- A series of entire functions whose terms are, near every point, eventually dominated by a
summable sequence defines an entire function. -/
theorem analyticOnNhd_tsum_of_eventually_dominated {F : ℕ → ℂ → ℂ}
    (hF : ∀ n, Differentiable ℂ (F n)) (hsum : ∀ w, Summable fun n => F n w)
    (hdom : ∀ w₀ : ℂ, ∃ U : Set ℂ, IsOpen U ∧ w₀ ∈ U ∧ ∃ N : ℕ, ∃ u : ℕ → ℝ, Summable u ∧
      ∀ n, N ≤ n → ∀ w ∈ U, ‖F n w‖ ≤ u n) :
    AnalyticOnNhd ℂ (fun w => ∑' n, F n w) univ := by
  intro w₀ _
  obtain ⟨U, hU, hw₀, N, u, hu, hle⟩ := hdom w₀
  have hsplit : ∀ w ∈ U,
      (∑' n, F n w) = ∑ n ∈ Finset.range N, F n w + ∑' k, F (k + N) w :=
    fun w _ => ((hsum w).sum_add_tsum_nat_add N).symm
  have htail : DifferentiableOn ℂ (fun w => ∑' k, F (k + N) w) U :=
    differentiableOn_tsum_of_summable_norm (u := fun k => u (k + N))
      (hu.comp_injective (add_left_injective N)) (fun k => (hF (k + N)).differentiableOn) hU
      (fun k w hw => hle (k + N) (by omega) w hw)
  have hfin : DifferentiableOn ℂ (fun w => ∑ n ∈ Finset.range N, F n w) U :=
    DifferentiableOn.fun_sum fun n _ => (hF n).differentiableOn
  have hdiff : DifferentiableOn ℂ (fun w => ∑' n, F n w) U :=
    (hfin.add htail).congr fun w hw => hsplit w hw
  exact hdiff.analyticAt (hU.mem_nhds hw₀)
