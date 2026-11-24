module

public import FormalResearch.ModularBootstrap.TwoLevel.WindowOptimumNodes
public import FormalResearch.ModularBootstrap.TwoLevel.WindowOptimumFunction
public import FormalResearch.Special.AiryClarkLabelAsym

/-!
# The Airy zeros and Clark nodes satisfy the node hypotheses (`virasoro_two_level.tex`, Proposition 2.3 `gt:2.3`)

For every `α` with `sin α ≠ 0`, the sequences `k ↦ |a_k|` and `k ↦ |z_k(α)|` satisfy `NodeHyp` from some index `k0`
on (`exists_clark_nodeHyp`): the interlacing `a_k < z_k < a_{k-1}`, the cube-root size and spacing of the Airy zeros
(`AiryZeroSpacing`) and the asymptotic half-way position of the nodes (`AiryClarkLabelAsym`).
-/

@[expose] public section

open Filter Topology

namespace FormalResearch.ModularBootstrap.TwoLevel

open FormalResearch.Special FormalResearch.SignUncertainty

theorem exists_clark_nodeHyp (α : ℝ) :
    ∃ k0 : ℕ, NodeHyp (fun k => -airyZero k) (fun k => -clarkNode α k) k0 := by
  have hfrac := tendsto_airyClarkNode_fraction (Real.cos α / Real.sin α)
  have hev : ∀ᶠ k : ℕ in atTop, |(airyZero k - airyClarkNode (Real.cos α / Real.sin α) (k + 1)) /
      (airyZero k - airyZero (k + 1)) - 1 / 2| < 1 / 20 := by
    have := (Metric.tendsto_nhds.1 hfrac) (1 / 20) (by norm_num)
    filter_upwards [this] with k hk
    simpa [Real.dist_eq] using hk
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  refine ⟨max 3 (N + 1), ?_⟩
  refine ⟨le_max_left _ _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    simpa using airyZero_neg k
  · intro k hk
    have := airyZero_lt_of_lt (n := k) (m := k + 1) hk (by omega)
    simpa using this
  · intro k hk
    have := airyClarkNode_lt_airyZero (n := k) hk (Real.cos α / Real.sin α)
    simp only [clarkNode, airyClarkAngleNode]
    linarith
  · intro k hk
    have := airyZero_lt_airyClarkNode (n := k) (by omega) (Real.cos α / Real.sin α)
    simp only [clarkNode, airyClarkAngleNode]
    linarith
  · intro k hk
    obtain ⟨-, h2⟩ := airyZero_gap_cube_bounds (n := k - 1) (by omega)
    have e : k - 1 + 1 = k := by omega
    rw [e] at h2
    have hk1 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    rw [hk1] at h2
    have e2 : (-airyZero k - -airyZero (k - 1)) = airyZero (k - 1) - airyZero k := by ring
    show ((k : ℝ) - 1) * ((fun k => -airyZero k) k - (fun k => -airyZero k) (k - 1)) ^ 3 ≤ 8.4
    simp only [e2]
    exact h2
  · intro j n hj hjn
    obtain ⟨h1, -⟩ := airyZero_separation hj hjn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hnj : (0 : ℝ) < (n : ℝ) - j := by
      have : (j : ℝ) < n := by exact_mod_cast hjn
      linarith
    have hr : ((n : ℝ) ^ (-(1 / 3) : ℝ)) ^ 3 = 1 / n := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
      norm_num
      rw [Real.rpow_neg_one]
    have hpos : 0 < (n : ℝ) ^ (-(1 / 3) : ℝ) := Real.rpow_pos_of_pos hn0 _
    have hc : (1.8 * ((n : ℝ) - j) * (n : ℝ) ^ (-(1 / 3) : ℝ)) ^ 3 ≤
        (airyZero j - airyZero n) ^ 3 := by
      exact pow_le_pow_left₀ (by positivity) h1 3
    have e : (1.8 * ((n : ℝ) - j) * (n : ℝ) ^ (-(1 / 3) : ℝ)) ^ 3 =
        5.832 * ((n : ℝ) - j) ^ 3 / n := by
      rw [mul_pow, mul_pow, hr]; ring
    rw [e] at hc
    rw [div_le_iff₀ hn0] at hc
    have : (-airyZero n - -airyZero j) = airyZero j - airyZero n := by ring
    simp only [this]
    nlinarith [pow_nonneg hnj.le 3]
  · intro k hk
    simpa using (airyZero_abs_cube_bounds hk).1
  · intro k hk
    simpa using (airyZero_abs_cube_bounds hk).2
  · intro k hk
    have hk3 : N + 1 ≤ k := (le_max_right _ _).trans hk
    have hk2 : 2 ≤ k - 1 := by have := le_max_left 3 (N + 1); omega
    have hb := hN (k - 1) (by omega)
    have e : k - 1 + 1 = k := by omega
    rw [e] at hb
    have hg : 0 < airyZero (k - 1) - airyZero k := by
      have := airyZero_strictAnti (n := k - 1) (by omega)
      rw [e] at this
      linarith
    have hb' := abs_lt.mp hb
    have key : (airyZero (k - 1) - airyClarkNode (Real.cos α / Real.sin α) k) /
        (airyZero (k - 1) - airyZero k) = ((-clarkNode α k) - -airyZero (k - 1)) /
          ((-airyZero k) - -airyZero (k - 1)) := by
      simp only [clarkNode, airyClarkAngleNode]; ring
    rw [key] at hb'
    obtain ⟨l, u⟩ := hb'
    have hg' : 0 < (-airyZero k) - -airyZero (k - 1) := by linarith
    set f := ((-clarkNode α k) - -airyZero (k - 1)) / ((-airyZero k) - -airyZero (k - 1)) with hf
    have hfe : f * ((-airyZero k) - -airyZero (k - 1)) = (-clarkNode α k) - -airyZero (k - 1) := by
      rw [hf]; field_simp
    have hmul1 : 9 / 20 * ((-airyZero k) - -airyZero (k - 1)) ≤ f * ((-airyZero k) - -airyZero (k - 1)) :=
      mul_le_mul_of_nonneg_right (by linarith) hg'.le
    have hmul2 : f * ((-airyZero k) - -airyZero (k - 1)) ≤ 11 / 20 * ((-airyZero k) - -airyZero (k - 1)) :=
      mul_le_mul_of_nonneg_right (by linarith) hg'.le
    constructor <;> linarith

end FormalResearch.ModularBootstrap.TwoLevel
