module

public import Mathlib.Analysis.Complex.AbelLimit
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The alternating series `∑ (-1)^n/(n+2) = 1 - log 2`

Generic.  **Proved** by the alternating series test, Abel's limit theorem and the power series of `log(1+x)`.
-/

@[expose] public section

open Finset Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

theorem tendsto_altHarm :
    Tendsto (fun N : ℕ => ∑ n ∈ range N, (-1 : ℝ) ^ n / ((n : ℝ) + 2)) atTop (𝓝 (1 - Real.log 2)) := by
  have hanti : Antitone (fun n : ℕ => 1 / ((n : ℝ) + 2)) := by
    intro a b hab
    have : (a : ℝ) ≤ b := by exact_mod_cast hab
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have hzero : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
    have : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    simp only [one_div]; exact this.inv_tendsto_atTop
  obtain ⟨l, hl⟩ := hanti.tendsto_alternating_series_of_tendsto_zero hzero
  have hl' : Tendsto (fun N : ℕ => ∑ n ∈ range N, (-1 : ℝ) ^ n / ((n : ℝ) + 2)) atTop (𝓝 l) := by
    refine hl.congr (fun N => ?_)
    refine sum_congr rfl (fun n _ => ?_)
    ring
  have hA := Real.tendsto_tsum_powerSeries_nhdsWithin_lt
    (f := fun n : ℕ => (-1 : ℝ) ^ n / ((n : ℝ) + 2)) hl'
  have hg : Tendsto (fun x : ℝ => (x - Real.log (1 + x)) / x ^ 2) (𝓝[<] 1) (𝓝 (1 - Real.log 2)) := by
    have hc : ContinuousAt (fun x : ℝ => (x - Real.log (1 + x)) / x ^ 2) 1 := by
      refine ContinuousAt.div (continuousAt_id.sub (ContinuousAt.log (by fun_prop) (by norm_num)))
        (by fun_prop) (by norm_num)
    have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Iio (1 : ℝ)))
    simpa [one_add_one_eq_two] using this
  have hev : ∀ᶠ x : ℝ in 𝓝[<] 1,
      ∑' n : ℕ, (-1 : ℝ) ^ n / ((n : ℝ) + 2) * x ^ n = (x - Real.log (1 + x)) / x ^ 2 := by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with x hx
    have hx0 : 0 < x := hx.1
    have hs := Real.hasSum_pow_div_log_of_abs_lt_one (x := -x) (by rw [abs_neg, abs_of_pos hx0]; exact hx.2)
    have hs2 := (hasSum_nat_add_iff' 1).mpr hs
    simp only [Finset.range_one, Finset.sum_singleton] at hs2
    have h3 := hs2.mul_left (x ^ 2)⁻¹
    have hsum : HasSum (fun n : ℕ => (-1 : ℝ) ^ n / ((n : ℝ) + 2) * x ^ n) ((x - Real.log (1 + x)) / x ^ 2) := by
      convert h3 using 1
      · funext n
        push_cast
        rw [show n + 1 + 1 = n + 2 by ring, pow_add, neg_pow x n]
        field_simp
        ring
      · simp
        field_simp
        ring
    exact hsum.tsum_eq
  exact tendsto_nhds_unique (hA.congr' hev) hg |> fun h => h ▸ hl'

end FormalResearch.SignUncertainty
