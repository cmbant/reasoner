module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Analysis.PSeries

/-!
# `∑_{k≥2} (-1)^k / k³ = 1 - (3/4) ζ(3)`

Generic.  **Proved** by splitting into even and odd `k` (`∑ 1/(2k)³ = ζ(3)/8`).
-/

@[expose] public section

open Filter Topology Finset
open scoped Real

namespace FormalResearch.SignUncertainty.CtOuter

lemma zeta3_re_eq : (riemannZeta 3).re = ∑' n : ℕ, 1 / (n : ℝ) ^ 3 := by
  have h := zeta_nat_eq_tsum_of_gt_one (k := 3) (by norm_num)
  have e : ((3 : ℕ) : ℂ) = 3 := by norm_num
  rw [e] at h
  rw [h]
  have : (fun n : ℕ => 1 / (n : ℂ) ^ 3) = fun n : ℕ => ((1 / (n : ℝ) ^ 3 : ℝ) : ℂ) := by
    funext n; push_cast; rfl
  rw [this, ← Complex.ofReal_tsum, Complex.ofReal_re]

theorem tendsto_alt_zeta3 :
    Tendsto (fun N : ℕ => ∑ i ∈ range N, (-1 : ℝ) ^ i / ((i : ℝ) + 2) ^ 3) atTop
      (𝓝 (1 - 3 / 4 * (riemannZeta 3).re)) := by
  rw [zeta3_re_eq]
  set a : ℕ → ℝ := fun n => 1 / (n : ℝ) ^ 3 with ha
  have hsa : Summable a := Real.summable_one_div_nat_pow.mpr (by norm_num)
  set g : ℕ → ℝ := fun n => (-1 : ℝ) ^ n / (n : ℝ) ^ 3 with hg
  have hsg : Summable g := by
    refine Summable.of_norm_bounded hsa (fun n => ?_)
    simp only [hg, ha, norm_div, norm_pow, norm_neg, norm_one, one_pow, Real.norm_natCast, one_div]
    rfl
  have hE : ∀ k : ℕ, a (2 * k) = a k / 8 := by
    intro k
    simp only [ha]
    push_cast
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · have : (k : ℝ) ≠ 0 := by positivity
      field_simp
      ring
  have hsE : Summable (fun k => a (2 * k)) := by
    have := hsa.div_const 8
    exact this.congr (fun k => (hE k).symm)
  have hsO : Summable (fun k => a (2 * k + 1)) :=
    hsa.comp_injective (i := fun k : ℕ => 2 * k + 1) (by intro x y h; simp only at h; omega)
  have hZ := tsum_even_add_odd hsE hsO
  have hEv : ∑' k, a (2 * k) = (∑' n, a n) / 8 := by
    rw [tsum_congr hE, tsum_div_const]
  have hgE : ∀ k, g (2 * k) = a (2 * k) := by
    intro k; simp only [hg, ha]; rw [(even_two_mul k).neg_one_pow]
  have hgO : ∀ k, g (2 * k + 1) = -a (2 * k + 1) := by
    intro k; simp only [hg, ha]; rw [(odd_two_mul_add_one k).neg_one_pow]; ring
  have hsgE : Summable (fun k => g (2 * k)) := hsE.congr (fun k => (hgE k).symm)
  have hsgO : Summable (fun k => g (2 * k + 1)) := hsO.neg.congr (fun k => (hgO k).symm)
  have hG := tsum_even_add_odd hsgE hsgO
  have hGv : ∑' n, g n = -(3 / 4) * ∑' n, a n := by
    rw [← hG, tsum_congr hgE, tsum_congr hgO, tsum_neg, hEv]
    linarith only [hZ, hEv]
  have h2 := (hasSum_nat_add_iff' 2).mpr hsg.hasSum
  have e0 : ∑ i ∈ range 2, g i = -1 := by
    simp [Finset.sum_range_succ, hg]
  rw [e0, hGv] at h2
  have h3 := h2.tendsto_sum_nat
  convert h3 using 2
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [hg]
    push_cast
    rw [pow_add]
    norm_num
  · ring

/-- info: 'FormalResearch.SignUncertainty.CtOuter.tendsto_alt_zeta3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tendsto_alt_zeta3

end FormalResearch.SignUncertainty.CtOuter
