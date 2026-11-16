module

public import FormalResearch.Racah.P2AnalyticCarrierHahn

/-!
# The `O(N⁻²)` estimate for the even Hahn deformation (Weyl P2, `lem:evendeformation`)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, `lem:evendeformation`: "`q_d(ς; h²)` is monic of
degree `d` in `ς` with coefficients that are polynomials in `h²`, `q_d(ς; 0) = P̂_d^{(α,β)}(ς)`; in
particular `sup_{0≤ς≤1} |q_d(ς; N⁻²) - P̂_d^{(α,β)}(ς)| ≤ C N⁻²`".

`lem_evendeformation3` (`P2AnalyticCarrierHahn`) proves the structural part (monic, polynomial in `t = h²`,
Jacobi at `t = 0`, Hahn at admissible `N`, all four chambers).  Here:

* `evenHahn3_bound`: **the estimate**, `|q_d(ς; t) - P̂_d^{(α,β)}(ς)| ≤ C t` for `0 ≤ t ≤ 1`, `0 ≤ ς ≤ 1`
  (`t = N⁻²`; `C` depends on the labels and the rank only), for `α = |M-σ|`, `β = |M+σ|`.

* `evenHahn3_one_const`: for `d = 1` the Hahn zero does not move (`q_1(ς; t)` is independent of `t`).

The coefficients of `q_d` do not have the extra degree bound of the Racah case (there is no second scale), so
nothing further is stated in the paper for `3j`.
-/

@[expose] public section

namespace FormalResearch.Racah

open FormalResearch.Wigner Polynomial

/-- `|c(t) - c(0)| ≤ B t` for `0 ≤ t ≤ 1`. -/
lemma poly_sub_eval_zero_le (c : ℝ[X]) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, 0 ≤ t → t ≤ 1 → |c.eval t - c.eval 0| ≤ B * t := by
  have hd : X ∣ c - C (c.eval 0) := by
    rw [X_dvd_iff, coeff_sub, coeff_C_zero, coeff_zero_eq_eval_zero]; ring
  obtain ⟨g, hg⟩ := hd
  refine ⟨∑ j ∈ Finset.range (g.natDegree + 1), |g.coeff j|,
    Finset.sum_nonneg fun j _ => abs_nonneg _, fun t ht0 ht1 => ?_⟩
  have e : c.eval t - c.eval 0 = t * g.eval t := by
    have := congrArg (eval t) hg
    simp only [eval_sub, eval_C, eval_mul, eval_X] at this
    exact this
  rw [e, abs_mul, abs_of_nonneg ht0, mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ ht0
  rw [eval_eq_sum_range]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul, abs_pow, abs_of_nonneg ht0]
  calc |g.coeff j| * t ^ j ≤ |g.coeff j| * 1 :=
        mul_le_mul_of_nonneg_left (pow_le_one₀ ht0 ht1) (abs_nonneg _)
    _ = _ := mul_one _

/-- **The estimate of `lem:evendeformation`**: with `α = |M-σ|`, `β = |M+σ|` and `d = k`, there is `C` with
`|q_d(ς; t) - P̂_d^{(α,β)}(ς)| ≤ C t` for all `0 ≤ t ≤ 1` (`t = N⁻²`) and `0 ≤ ς ≤ 1`, where
`q_d(ς; t) = (evenHahn3 M σ k)(ς; t) = P̃_{L₀+k}(ς; t)/k_{3j}`. -/
theorem evenHahn3_bound (M σ : ℚ) (α β k : ℕ) (hα : |M - σ| = α) (hβ : |M + σ| = β) :
    ∃ C : ℝ, ∀ t τ : ℝ, 0 ≤ t → t ≤ 1 → 0 ≤ τ → τ ≤ 1 →
      |((evenHahn3 M σ k).map (evalRingHom t)).eval τ - (jacobiMonicTau α β k).eval τ| ≤ C * t := by
  have h0 := (lem_evendeformation3 M σ α β k hα hβ).2.2.1
  have hdeg : (evenHahn3 M σ k).natDegree ≤ k := (lem_evendeformation3 M σ α β k hα hβ).1
  choose B hB0 hB using fun i => poly_sub_eval_zero_le ((evenHahn3 M σ k).coeff i)
  refine ⟨∑ i ∈ Finset.range (k + 1), B i, fun t τ ht0 ht1 hτ0 hτ1 => ?_⟩
  have e : ∀ s : ℝ, ((evenHahn3 M σ k).map (evalRingHom s)).eval τ =
      ∑ i ∈ Finset.range (k + 1), ((evenHahn3 M σ k).coeff i).eval s * τ ^ i := by
    intro s
    rw [eval_eq_sum_range' (n := k + 1)
      (lt_of_le_of_lt (natDegree_map_le) (Nat.lt_succ_of_le hdeg))]
    simp [coeff_map]
  rw [← h0, e t, e 0, ← Finset.sum_sub_distrib, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [← sub_mul, abs_mul, abs_of_nonneg (pow_nonneg hτ0 i)]
  calc |((evenHahn3 M σ k).coeff i).eval t - ((evenHahn3 M σ k).coeff i).eval 0| * τ ^ i
      ≤ (B i * t) * 1 := mul_le_mul (hB i t ht0 ht1) (pow_le_one₀ hτ0 hτ1) (pow_nonneg hτ0 i)
        (mul_nonneg (hB0 i) ht0)
    _ = _ := by ring

/-- For `d = 1` the Hahn zero does not move (`lem:evendeformation`, remark after the proof): `q_1(ς; t)` does
not depend on `t`. -/
theorem evenHahn3_one_const (M σ : ℚ) (t : ℝ) :
    (evenHahn3 M σ 1).map (evalRingHom t) = (evenHahn3 M σ 1).map (evalRingHom 0) := by
  have h : ∀ s : ℝ, (ptilde3Poly M σ 1).map (evalRingHom s) =
      (ptilde3Poly M σ 1).map (evalRingHom 0) := by
    intro s
    simp only [ptilde3Poly]
    split_ifs
    · simp
    · simp [step3P]
  unfold evenHahn3
  rw [Polynomial.map_mul, Polynomial.map_mul, h t]
  simp

end FormalResearch.Racah

/-- info: 'FormalResearch.Racah.evenHahn3_one_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Racah.evenHahn3_one_const

/-- info: 'FormalResearch.Racah.evenHahn3_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Racah.evenHahn3_bound
