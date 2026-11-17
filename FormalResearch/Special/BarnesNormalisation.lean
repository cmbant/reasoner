module

public import FormalResearch.Special.BarnesLogSeries

/-!
# Normalisation `G(2) = 1` of Barnes' function (Stirling's formula)

`barnesLogSeries 1 = ∑_{k≥1} (k log(1+1/k) - 1 + 1/(2k))
 = 1 + γ/2 - (1/2) log(2π)`.  The partial sums are
`N log(N+1) - log N! - N + H_N/2` (telescoping), and the limit follows from Stirling's formula
(`Stirling.tendsto_stirlingSeq_sqrt_pi`) and `H_N - log N → γ`.  This is the only place where the
constant `(1/2) log (2π)` of the Weierstrass product is used.
-/

@[expose] public section

namespace FormalResearch.Special.Barnes

open Filter Topology Set

local notation "γ" => Real.eulerMascheroniConstant

/-- Real form of the series term at `z = 1`. -/
noncomputable def barnesRealTerm (k : ℕ) : ℝ :=
  ((k : ℝ) + 1) * Real.log (1 + 1 / ((k : ℝ) + 1)) - 1 + 1 / (2 * ((k : ℝ) + 1))

lemma barnesTerm_one (k : ℕ) : barnesTerm k 1 = ((barnesRealTerm k : ℝ) : ℂ) := by
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  unfold barnesTerm barnesRealTerm
  have h1 : (1 : ℂ) + 1 / ((k : ℂ) + 1) = ((1 + 1 / ((k : ℝ) + 1) : ℝ) : ℂ) := by push_cast; rfl
  rw [h1, ← Complex.ofReal_log (by positivity)]
  push_cast
  ring

lemma sum_barnesRealTerm (N : ℕ) :
    ∑ k ∈ Finset.range N, barnesRealTerm k =
      (N : ℝ) * Real.log ((N : ℝ) + 1) - Real.log (N.factorial) - N + (harmonic N : ℝ) / 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, barnesRealTerm, Nat.factorial_succ, harmonic_succ]
    have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have hf : (0 : ℝ) < (N.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos N
    push_cast
    rw [Real.log_mul hN.ne' hf.ne']
    have h2 : Real.log (1 + 1 / ((N : ℝ) + 1)) = Real.log ((N : ℝ) + 2) - Real.log ((N : ℝ) + 1) := by
      rw [← Real.log_div (by positivity) hN.ne']
      congr 1; field_simp; ring
    rw [h2, show ((N : ℝ) + 1 + 1) = (N : ℝ) + 2 by ring]
    field_simp
    ring

lemma tendsto_mul_log_one_add_inv :
    Tendsto (fun N : ℕ => (N : ℝ) * Real.log (1 + 1 / (N : ℝ))) atTop (𝓝 1) := by
  have h := hasDerivAt_iff_tendsto_slope_zero.mp (Real.hasDerivAt_log (one_ne_zero))
  have hN : Tendsto (fun N : ℕ => 1 / (N : ℝ)) atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨by simpa using tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ),
      ?_⟩
    filter_upwards [eventually_gt_atTop 0] with N hN
    have : (0 : ℝ) < N := by exact_mod_cast hN
    simp [this.ne']
  have h2 := h.comp hN
  simp only [inv_one] at h2
  refine h2.congr fun N => ?_
  simp [Real.log_one]


lemma log_factorial_stirling {N : ℕ} (hN : 1 ≤ N) :
    Real.log (N.factorial) = Real.log (Stirling.stirlingSeq N) + Real.log 2 / 2 + Real.log N / 2 +
      N * Real.log N - N := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hf : (0 : ℝ) < (N.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos N
  have hs : 0 < Stirling.stirlingSeq N := by
    unfold Stirling.stirlingSeq
    have : 0 < Real.sqrt (2 * (N : ℝ)) := Real.sqrt_pos.mpr (by positivity)
    positivity
  have h : (N.factorial : ℝ) = Stirling.stirlingSeq N * (Real.sqrt (2 * N) * ((N : ℝ) / Real.exp 1) ^ N) := by
    unfold Stirling.stirlingSeq
    have : 0 < Real.sqrt (2 * (N : ℝ)) := Real.sqrt_pos.mpr (by positivity)
    field_simp
  rw [h, Real.log_mul hs.ne' (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_sqrt (by positivity), Real.log_div hNp.ne' (Real.exp_pos 1).ne',
    Real.log_exp, Real.log_mul (by norm_num) hNp.ne']
  ring

lemma tendsto_sum_barnesRealTerm :
    Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, barnesRealTerm k) atTop
      (𝓝 (1 - Real.log (Real.sqrt Real.pi) - Real.log 2 / 2 + γ / 2)) := by
  have hs := Stirling.tendsto_stirlingSeq_sqrt_pi
  have hlog : Tendsto (fun N : ℕ => Real.log (Stirling.stirlingSeq N)) atTop
      (𝓝 (Real.log (Real.sqrt Real.pi))) :=
    (Real.continuousAt_log (Real.sqrt_pos.mpr Real.pi_pos).ne').tendsto.comp hs
  have hH := Real.tendsto_harmonic_sub_log
  have := ((tendsto_mul_log_one_add_inv.sub hlog).sub_const (Real.log 2 / 2)).add (hH.div_const 2)
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  rw [sum_barnesRealTerm, log_factorial_stirling hN]
  have h2 : Real.log (1 + 1 / (N : ℝ)) = Real.log ((N : ℝ) + 1) - Real.log N := by
    rw [← Real.log_div (by positivity) hNp.ne']
    congr 1; field_simp
  rw [h2]
  ring

/-- `∑_{k≥1} (k log(1+1/k) - 1 + 1/(2k)) = 1 + γ/2 - (1/2) log(2π)` (Stirling). -/
theorem barnesLogSeries_one :
    barnesLogSeries 1 = ((1 + γ / 2 - Real.log (2 * Real.pi) / 2 : ℝ) : ℂ) := by
  have hsum : Summable (fun k : ℕ => barnesRealTerm k) := by
    have := summable_barnesTerm (z := 1) (by simp)
    refine Complex.summable_ofReal.mp (this.congr fun k => ?_)
    rw [barnesTerm_one]
  have h1 : HasSum (fun k : ℕ => barnesRealTerm k) (1 + γ / 2 - Real.log (2 * Real.pi) / 2) := by
    rw [hsum.hasSum_iff_tendsto_nat]
    convert tendsto_sum_barnesRealTerm using 2
    rw [Real.log_sqrt Real.pi_pos.le, Real.log_mul (by norm_num) Real.pi_pos.ne']
    ring
  have h2 := (Complex.hasSum_ofReal.mpr h1)
  unfold barnesLogSeries
  simp_rw [barnesTerm_one]
  exact h2.tsum_eq

end FormalResearch.Special.Barnes
