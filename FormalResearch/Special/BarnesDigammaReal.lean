module

public import Mathlib

/-!
# Gauss' series for the digamma function on the positive real axis

For real `x > 0`, with `f = log ∘ Γ` and `ψ = f'`,

`ψ(x) = -γ + ∑_{k ≥ 0} (1/(k+1) - 1/(k+x))`   (DLMF 5.7.6, in the form `ψ(1+z)+γ = ∑ z/(k(k+z))`).

Proof (this file): `f` is convex (Bohr–Mollerup, Mathlib `Real.convexOn_log_Gamma`) and
`f(x+1) = f(x) + log x`, so the slopes of `f` give `log (y-1) ≤ ψ(y) ≤ log y` for `y > 1`, and
`ψ(x+n) = ψ(x) + ∑_{k<n} 1/(x+k)`; together with `H_n - log n → γ` this identifies the limit of the
partial sums.  The extension to the right half-plane is `BarnesDigamma`.

Not formalised here: the series for `Re z ≤ 0` (it is not needed downstream).
-/

@[expose] public section

namespace FormalResearch.Special.Barnes

open Filter Topology Set

local notation "γ" => Real.eulerMascheroniConstant

/-- `log ∘ Γ` on the reals. -/
noncomputable abbrev logGammaR : ℝ → ℝ := Real.log ∘ Real.Gamma

lemma logGammaR_differentiableAt {x : ℝ} (hx : 0 < x) : DifferentiableAt ℝ logGammaR x := by
  refine (Real.differentiableAt_Gamma ?_).log (Real.Gamma_ne_zero ?_) <;>
    exact fun m => ne_of_gt (by linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)])

lemma logGammaR_rec {x : ℝ} (hx : 0 < x) :
    logGammaR (x + 1) = logGammaR x + Real.log x := by
  simp only [logGammaR, Function.comp_apply, Real.Gamma_add_one hx.ne',
    Real.log_mul hx.ne' (Real.Gamma_pos_of_pos hx).ne', add_comm]

lemma deriv_logGammaR_rec {x : ℝ} (hx : 0 < x) :
    deriv logGammaR (x + 1) = deriv logGammaR x + 1 / x := by
  rw [← deriv_comp_add_const, one_div, ← Real.deriv_log,
    ← deriv_add (logGammaR_differentiableAt hx) (Real.differentiableAt_log hx.ne')]
  apply EventuallyEq.deriv_eq
  filter_upwards [eventually_gt_nhds hx] with y hy using logGammaR_rec hy

lemma deriv_logGammaR_add_nat {x : ℝ} (hx : 0 < x) (n : ℕ) :
    deriv logGammaR (x + n) =
      deriv logGammaR x + ∑ k ∈ Finset.range n, 1 / (x + k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hpos : 0 < x + n := by positivity
    rw [show x + ((n + 1 : ℕ) : ℝ) = (x + n) + 1 by push_cast; ring, deriv_logGammaR_rec hpos, ih,
      Finset.sum_range_succ]
    ring

/-- Slope bounds from convexity: `log (y-1) ≤ ψ(y) ≤ log y` for `y > 1`. -/
lemma deriv_logGammaR_bounds {y : ℝ} (hy : 1 < y) :
    Real.log (y - 1) ≤ deriv logGammaR y ∧ deriv logGammaR y ≤ Real.log y := by
  have hc : ConvexOn ℝ (Ioi 0) logGammaR := Real.convexOn_log_Gamma
  have hy0 : 0 < y := by linarith
  have hy1 : 0 < y - 1 := by linarith
  constructor
  · refine le_trans (le_of_eq ?_)
      (hc.slope_le_deriv (mem_Ioi.mpr hy1) (mem_Ioi.mpr hy0) (by linarith)
        (logGammaR_differentiableAt hy0))
    rw [slope_def_field, show y - (y - 1) = (1 : ℝ) by ring, div_one,
      show logGammaR y = logGammaR ((y - 1) + 1) by ring_nf, logGammaR_rec hy1]
    ring
  · refine le_trans (hc.deriv_le_slope (mem_Ioi.mpr hy0) (mem_Ioi.mpr (by linarith : (0:ℝ) < y + 1))
      (by linarith) (logGammaR_differentiableAt hy0)) (le_of_eq ?_)
    rw [slope_def_field, show y + 1 - y = (1 : ℝ) by ring, div_one, logGammaR_rec hy0]
    ring

/-- The Gauss partial sums on the real axis. -/
lemma partial_sum_real {x : ℝ} (hx : 0 < x) (n : ℕ) :
    ∑ k ∈ Finset.range n, (1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + x)) =
      (harmonic n : ℝ) - (deriv logGammaR (x + n) - deriv logGammaR x) := by
  rw [deriv_logGammaR_add_nat hx n, Finset.sum_sub_distrib, add_sub_cancel_left]
  congr 1
  · rw [harmonic]; push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    simp
  · refine Finset.sum_congr rfl fun k _ => ?_
    simp [add_comm]

lemma tendsto_log_add_sub_log (c : ℝ) :
    Tendsto (fun n : ℕ => Real.log (c + n) - Real.log n) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => 1 + c / (n : ℝ)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat c)
  have h2 := ((Real.continuousAt_log one_ne_zero).tendsto.comp h)
  rw [Real.log_one] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop (Nat.ceil |c|)] with n hn
  have hn' : (|c| : ℝ) < n := lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hn)
  have hnpos : (0 : ℝ) < n := lt_of_le_of_lt (abs_nonneg c) hn'
  have hcn : 0 < c + n := by linarith [neg_abs_le c]
  simp only [Function.comp_apply]
  rw [← Real.log_div hcn.ne' hnpos.ne']
  congr 1
  field_simp
  ring

lemma tendsto_deriv_logGammaR_sub_log {x : ℝ} (hx : 0 < x) :
    Tendsto (fun n : ℕ => deriv logGammaR (x + n) - Real.log n) atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (tendsto_log_add_sub_log (x - 1))
    (tendsto_log_add_sub_log x) ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have := (deriv_logGammaR_bounds (y := x + n) (by linarith)).1
    rw [show x + n - 1 = (x - 1) + n by ring] at this
    linarith
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have := (deriv_logGammaR_bounds (y := x + n) (by linarith)).2
    linarith

/-- The Gauss series term. -/
noncomputable def psiTerm (z : ℂ) (k : ℕ) : ℂ := 1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + z)

lemma psiTerm_eq {z : ℂ} {k : ℕ} (hz : 0 ≤ z.re) (hk : 1 ≤ k) :
    psiTerm z k = (z - 1) / (((k : ℂ) + 1) * ((k : ℂ) + z)) := by
  have hk1 : (k : ℂ) + 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
  have hk2 : (k : ℂ) + z ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  unfold psiTerm
  field_simp
  ring

lemma norm_psiTerm_le {z : ℂ} (hz : 0 ≤ z.re) {k : ℕ} (hk : 1 ≤ k) :
    ‖psiTerm z k‖ ≤ ‖z - 1‖ * (1 / (k : ℝ) ^ 2) := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  rw [psiTerm_eq hz hk, norm_div, norm_mul]
  have h1 : (k : ℝ) ≤ ‖(k : ℂ) + 1‖ := by
    refine le_trans ?_ (Complex.re_le_norm _)
    simp
  have h2 : (k : ℝ) ≤ ‖(k : ℂ) + z‖ := by
    refine le_trans ?_ (Complex.re_le_norm _)
    simp [hz]
  have hkpos : (0 : ℝ) < k := by linarith
  calc ‖z - 1‖ / (‖(k : ℂ) + 1‖ * ‖(k : ℂ) + z‖) ≤ ‖z - 1‖ / ((k : ℝ) * k) :=
        div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
          (mul_le_mul h1 h2 hkpos.le (by linarith))
    _ = ‖z - 1‖ * (1 / (k : ℝ) ^ 2) := by field_simp

/-- Summability of the Gauss series terms, for complex `z` with `0 ≤ Re z`. -/
lemma summable_psiTerm {z : ℂ} (hz : 0 ≤ z.re) : Summable (psiTerm z) := by
  rw [← summable_nat_add_iff (f := psiTerm z) 1]
  refine Summable.of_norm_bounded (g := fun k : ℕ => ‖z - 1‖ * (1 / ((k + 1 : ℕ) : ℝ) ^ 2)) ?_
    (fun k => norm_psiTerm_le hz (by omega))
  refine Summable.mul_left _ ?_
  exact (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))

/-- **Gauss' series for `ψ = (log Γ)'` on the positive real axis.** -/
lemma hasSum_psiTerm_real {x : ℝ} (hx : 0 < x) :
    HasSum (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1) - 1 / ((k : ℝ) + x))
      (deriv logGammaR x + γ) := by
  have hs : Summable (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1) - 1 / ((k : ℝ) + x)) := by
    have := (summable_psiTerm (z := (x : ℂ)) (by simpa using hx.le))
    refine Complex.summable_ofReal.mp (this.congr fun k => ?_)
    simp [psiTerm]
  rw [hs.hasSum_iff_tendsto_nat]
  simp_rw [partial_sum_real hx]
  have h1 := Real.tendsto_harmonic_sub_log
  have h2 := tendsto_deriv_logGammaR_sub_log hx
  have := (h1.sub h2).add_const (deriv logGammaR x)
  rw [show γ - 0 + deriv logGammaR x = deriv logGammaR x + γ by ring] at this
  refine this.congr fun n => ?_
  ring


/-- info: 'FormalResearch.Special.Barnes.hasSum_psiTerm_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasSum_psiTerm_real

end FormalResearch.Special.Barnes
