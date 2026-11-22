module

public import Mathlib.Analysis.BoundedVariation
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Van der Corput First- and Second-Derivative Estimates

Source: `CFT/common/two_edge_bootstrap.tex` (used by Lemma TE.1a).

## Main theorems

* `norm_integral_mul_deriv_le_of_boundedVariation`: integration-by-parts bound on `[a, b]` for continuous BV amplitudes.
* `van_der_corput_first_comp`, `van_der_corput_first`: first-derivative van der Corput estimates.
* `van_der_corput_second_comp`, `van_der_corput_second`: second-derivative van der Corput estimates.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real ENNReal NNReal Interval

namespace FormalResearch.Analysis

/-! ### Part 4: Lemma TE.1a — Van der Corput and Oscillatory Edge Estimate -/

section VanDerCorput

private lemma sum_range_abel {n : ℕ} (u F : ℕ → ℂ) :
    ∑ k ∈ Finset.range (n + 1), u k * (F (k + 1) - F k) =
      u n * F (n + 1) - u 0 * F 0 - ∑ k ∈ Finset.range n, (u (k + 1) - u k) * F (k + 1) := by
  induction n with
  | zero => simp; ring
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ring

/-- Integration by parts bound on `[a, b]` for a continuous bounded-variation amplitude `h` against
a `C¹` oscillatory factor `F'`. -/
lemma norm_integral_mul_deriv_le_of_boundedVariation {a b : ℝ} (hab : a ≤ b)
    {h : ℝ → ℂ} (hh_cont : ContinuousOn h (Icc a b)) (hh_bv : BoundedVariationOn h (Icc a b))
    {F F' : ℝ → ℂ} (hF : ∀ x ∈ Icc a b, HasDerivAt F (F' x) x)
    (hF'_cont : ContinuousOn F' (Icc a b)) {B : ℝ} (hB_nn : 0 ≤ B)
    (hF_bound : ∀ x ∈ Icc a b, ‖F x‖ ≤ B) :
    ‖∫ x in a..b, h x * F' x‖ ≤
      B * (‖h a‖ + ‖h b‖ + (eVariationOn h (Icc a b)).toReal) := by
  rcases eq_or_lt_of_le hab with rfl | hab_lt
  · simp only [intervalIntegral.integral_same, norm_zero]
    have : 0 ≤ ‖h a‖ + ‖h a‖ + (eVariationOn h (Icc a a)).toReal := by positivity
    positivity
  obtain ⟨M', hM'⟩ := isCompact_Icc.exists_bound_of_continuousOn hF'_cont
  have hM'_nn : 0 ≤ M' := by
    have := hM' a (left_mem_Icc.mpr hab)
    exact (norm_nonneg _).trans this
  have h_unif := isCompact_Icc.uniformContinuousOn_of_continuous hh_cont
  rw [Metric.uniformContinuousOn_iff] at h_unif
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  set ε₀ := ε / (2 * (B + M' * (b - a) + 1))
  have hε₀ : 0 < ε₀ := by positivity
  obtain ⟨δ, hδ_pos, hδ⟩ := h_unif ε₀ hε₀
  obtain ⟨n, hn⟩ := exists_nat_gt ((b - a) / δ)
  have hn_pos : 0 < n := by
    by_contra h0
    have : n = 0 := by omega
    subst this
    have : (0 : ℝ) < (b - a) / δ := div_pos (sub_pos.mpr hab_lt) hδ_pos
    linarith
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  let x : ℕ → ℝ := fun k => a + (k : ℝ) * (b - a) / (m + 1 : ℝ)
  have hx_mono : Monotone x := fun i j hij => by
    dsimp [x]
    have : (i : ℝ) ≤ j := Nat.cast_le.mpr hij
    gcongr
  have hx0 : x 0 = a := by simp [x]
  have hxn : x (m + 1) = b := by
    dsimp [x]; push_cast; field_simp; ring
  have hx_mem : ∀ k ≤ m + 1, x k ∈ Icc a b := fun k hk => by
    rw [← hx0, ← hxn]
    exact ⟨hx_mono (Nat.zero_le k), hx_mono hk⟩
  have hstep : ∀ k ≤ m, x (k + 1) - x k = (b - a) / (m + 1 : ℝ) := fun k _ => by
    dsimp [x]; push_cast; ring
  have hstep_lt : (b - a) / (m + 1 : ℝ) < δ := by
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < m + 1)]
    have h1 := hn
    rw [div_lt_iff₀ hδ_pos] at h1
    push_cast at h1 ⊢
    linarith
  have hi_tot : IntervalIntegrable (fun t => h t * F' t) volume a b :=
    (hh_cont.mul hF'_cont).intervalIntegrable_of_Icc hab
  have hsum_int : ∫ t in a..b, h t * F' t =
      ∑ k ∈ Finset.range (m + 1), ∫ t in x k..x (k + 1), h t * F' t := by
    rw [← hx0, ← hxn]
    symm
    refine intervalIntegral.sum_integral_adjacent_intervals fun k hk => ?_
    refine hi_tot.mono_set (uIcc_subset_uIcc ?_ ?_)
    · rw [uIcc_of_le hab]; exact hx_mem k (by omega)
    · rw [uIcc_of_le hab]; exact hx_mem (k + 1) (by omega)
  have hdecomp : ∀ k ∈ Finset.range (m + 1),
      ∫ t in x k..x (k + 1), h t * F' t =
        h (x k) * (F (x (k + 1)) - F (x k)) +
          ∫ t in x k..x (k + 1), (h t - h (x k)) * F' t := fun k hk => by
    have hk_le : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hle_k : x k ≤ x (k + 1) := hx_mono (Nat.le_succ k)
    have hsub_ic : Icc (x k) (x (k + 1)) ⊆ Icc a b :=
      Icc_subset_Icc (hx_mem k (by omega)).1 (hx_mem (k + 1) (by omega)).2
    have hcont1 : ContinuousOn (fun t => h (x k) * F' t) (Icc (x k) (x (k + 1))) :=
      continuousOn_const.mul (hF'_cont.mono hsub_ic)
    have hi1 : IntervalIntegrable (fun t => h (x k) * F' t) volume (x k) (x (k + 1)) :=
      hcont1.intervalIntegrable_of_Icc hle_k
    have hcont2 : ContinuousOn (fun t => (h t - h (x k)) * F' t) (Icc (x k) (x (k + 1))) :=
      ((hh_cont.mono hsub_ic).sub continuousOn_const).mul (hF'_cont.mono hsub_ic)
    have hi2 : IntervalIntegrable (fun t => (h t - h (x k)) * F' t) volume (x k) (x (k + 1)) :=
      hcont2.intervalIntegrable_of_Icc hle_k
    have h_ftc : ∫ t in x k..x (k + 1), h (x k) * F' t = h (x k) * (F (x (k + 1)) - F (x k)) := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun t ht => hF t (hsub_ic (uIcc_of_le hle_k ▸ ht)))
          ((hF'_cont.mono hsub_ic).intervalIntegrable_of_Icc hle_k)]
    have h_split : (fun t => h t * F' t) = fun t => h (x k) * F' t + (h t - h (x k)) * F' t := by
      ext t; ring
    rw [h_split, intervalIntegral.integral_add hi1 hi2, h_ftc]
  have hsum_split : ∫ t in a..b, h t * F' t =
      (∑ k ∈ Finset.range (m + 1), h (x k) * (F (x (k + 1)) - F (x k))) +
        ∑ k ∈ Finset.range (m + 1), ∫ t in x k..x (k + 1), (h t - h (x k)) * F' t := by
    rw [hsum_int, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl hdecomp
  have h_abel : ∑ k ∈ Finset.range (m + 1), h (x k) * (F (x (k + 1)) - F (x k)) =
      h (x m) * F b - h a * F a -
        ∑ k ∈ Finset.range m, (h (x (k + 1)) - h (x k)) * F (x (k + 1)) := by
    have h1 := sum_range_abel (n := m) (fun k => h (x k)) (fun k => F (x k))
    simpa only [hx0, hxn] using h1
  have h_xm_dist : dist (x m) b < δ := by
    rw [← hxn, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr (hx_mono (Nat.le_succ m))), neg_sub,
      hstep m le_rfl]
    exact hstep_lt
  have h_xm_err : ‖h (x m) - h b‖ ≤ ε₀ := by
    have := hδ (x m) (hx_mem m (by omega)) b (right_mem_Icc.mpr hab) h_xm_dist
    simpa [dist_eq_norm] using this.le
  have h_abel_norm : ‖∑ k ∈ Finset.range (m + 1), h (x k) * (F (x (k + 1)) - F (x k))‖ ≤
      B * (‖h a‖ + ‖h b‖ + (eVariationOn h (Icc a b)).toReal) + B * ε₀ := by
    rw [h_abel]
    have h1 : ‖h (x m) * F b‖ ≤ (‖h b‖ + ε₀) * B := by
      have hxb : ‖h (x m)‖ ≤ ‖h b‖ + ε₀ := by
        calc ‖h (x m)‖ = ‖h b + (h (x m) - h b)‖ := by ring_nf
          _ ≤ ‖h b‖ + ‖h (x m) - h b‖ := norm_add_le _ _
          _ ≤ ‖h b‖ + ε₀ := by linarith
      calc ‖h (x m) * F b‖ = ‖h (x m)‖ * ‖F b‖ := norm_mul _ _
        _ ≤ (‖h b‖ + ε₀) * B := mul_le_mul hxb (hF_bound b (right_mem_Icc.mpr hab)) (norm_nonneg _) (by positivity)
    have h2 : ‖h a * F a‖ ≤ ‖h a‖ * B := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hF_bound a (left_mem_Icc.mpr hab)) (norm_nonneg _)
    have h3 : ‖∑ k ∈ Finset.range m, (h (x (k + 1)) - h (x k)) * F (x (k + 1))‖ ≤
        B * (eVariationOn h (Icc a b)).toReal := by
      calc ‖∑ k ∈ Finset.range m, (h (x (k + 1)) - h (x k)) * F (x (k + 1))‖
          ≤ ∑ k ∈ Finset.range m, ‖(h (x (k + 1)) - h (x k)) * F (x (k + 1))‖ := norm_sum_le _ _
        _ ≤ ∑ k ∈ Finset.range m, ‖h (x (k + 1)) - h (x k)‖ * B := by
            refine Finset.sum_le_sum fun k hk => ?_
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_left (hF_bound _ (hx_mem (k + 1) (by have := Finset.mem_range.mp hk; omega)))
              (norm_nonneg _)
        _ = B * ∑ k ∈ Finset.range m, ‖h (x (k + 1)) - h (x k)‖ := by rw [← Finset.sum_mul, mul_comm]
        _ ≤ B * (eVariationOn h (Icc a b)).toReal := by
            gcongr
            have h_enn : (∑ k ∈ Finset.range m, ENNReal.ofReal ‖h (x (k + 1)) - h (x k)‖) ≤
                eVariationOn h (Icc a b) := by
              have heq : (∑ k ∈ Finset.range m, ENNReal.ofReal ‖h (x (k + 1)) - h (x k)‖) =
                  ∑ k ∈ Finset.range m, edist (h (x (k + 1))) (h (x k)) := by
                refine Finset.sum_congr rfl fun k _ => ?_
                rw [edist_dist, dist_eq_norm]
              rw [heq]
              exact eVariationOn.sum_le_of_monotoneOn_Iic (hx_mono.monotoneOn _)
                fun i hi => hx_mem i (by omega)
            rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => norm_nonneg _)] at h_enn
            calc ∑ k ∈ Finset.range m, ‖h (x (k + 1)) - h (x k)‖
                = (ENNReal.ofReal (∑ k ∈ Finset.range m, ‖h (x (k + 1)) - h (x k)‖)).toReal :=
                  (ENNReal.toReal_ofReal (Finset.sum_nonneg fun _ _ => norm_nonneg _)).symm
              _ ≤ (eVariationOn h (Icc a b)).toReal := ENNReal.toReal_mono hh_bv h_enn
    calc ‖h (x m) * F b - h a * F a -
            ∑ k ∈ Finset.range m, (h (x (k + 1)) - h (x k)) * F (x (k + 1))‖
        ≤ ‖h (x m) * F b‖ + ‖h a * F a‖ +
            ‖∑ k ∈ Finset.range m, (h (x (k + 1)) - h (x k)) * F (x (k + 1))‖ := by
          calc _ ≤ ‖h (x m) * F b - h a * F a‖ +
                  ‖∑ k ∈ Finset.range m, (h (x (k + 1)) - h (x k)) * F (x (k + 1))‖ := norm_sub_le _ _
            _ ≤ ‖h (x m) * F b‖ + ‖h a * F a‖ + _ := add_le_add (norm_sub_le _ _) le_rfl
      _ ≤ (‖h b‖ + ε₀) * B + ‖h a‖ * B + B * (eVariationOn h (Icc a b)).toReal := by linarith
      _ = B * (‖h a‖ + ‖h b‖ + (eVariationOn h (Icc a b)).toReal) + B * ε₀ := by ring
  have h_err_norm : ‖∑ k ∈ Finset.range (m + 1), ∫ t in x k..x (k + 1), (h t - h (x k)) * F' t‖ ≤
      ε₀ * M' * (b - a) := by
    have hterm : ∀ k ∈ Finset.range (m + 1),
        ‖∫ t in x k..x (k + 1), (h t - h (x k)) * F' t‖ ≤ ε₀ * M' * (x (k + 1) - x k) := by
      intro k hk
      have hk_le : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have hle_k : x k ≤ x (k + 1) := hx_mono (Nat.le_succ k)
      rw [← abs_of_nonneg (sub_nonneg.mpr hle_k)]
      refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
      intro t ht
      rw [uIoc_of_le hle_k] at ht
      have ht_mem : t ∈ Icc a b :=
        ⟨(hx_mem k (by omega)).1.trans ht.1.le, ht.2.trans (hx_mem (k + 1) (by omega)).2⟩
      have hdist : dist t (x k) < δ := by
        rw [Real.dist_eq, abs_of_pos (sub_pos.mpr ht.1)]
        have hdiff_le : t - x k ≤ x (k + 1) - x k := by linarith [ht.2]
        exact hdiff_le.trans_lt (by rw [hstep k hk_le]; exact hstep_lt)
      have hhd : ‖h t - h (x k)‖ ≤ ε₀ := by
        have := hδ t ht_mem (x k) (hx_mem k (by omega)) hdist
        simpa [dist_eq_norm] using this.le
      have hFd : ‖F' t‖ ≤ M' := hM' t ht_mem
      rw [norm_mul]
      exact mul_le_mul hhd hFd (norm_nonneg _) hε₀.le
    calc ‖∑ k ∈ Finset.range (m + 1), ∫ t in x k..x (k + 1), (h t - h (x k)) * F' t‖
        ≤ ∑ k ∈ Finset.range (m + 1), ‖∫ t in x k..x (k + 1), (h t - h (x k)) * F' t‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.range (m + 1), ε₀ * M' * (x (k + 1) - x k) := Finset.sum_le_sum hterm
      _ = ε₀ * M' * ∑ k ∈ Finset.range (m + 1), (x (k + 1) - x k) := by rw [← Finset.mul_sum]
      _ = ε₀ * M' * (b - a) := by
          rw [Finset.sum_range_sub (f := x), hx0, hxn]
  have hε_small : (B + M' * (b - a)) * ε₀ < ε := by
    have hden_pos : 0 < B + M' * (b - a) + 1 := by positivity
    dsimp [ε₀]
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  calc ‖∫ t in a..b, h t * F' t‖
      ≤ ‖∑ k ∈ Finset.range (m + 1), h (x k) * (F (x (k + 1)) - F (x k))‖ +
          ‖∑ k ∈ Finset.range (m + 1), ∫ t in x k..x (k + 1), (h t - h (x k)) * F' t‖ := by
        rw [hsum_split]; exact norm_add_le _ _
    _ ≤ B * (‖h a‖ + ‖h b‖ + (eVariationOn h (Icc a b)).toReal) + B * ε₀ + ε₀ * M' * (b - a) := by
        linarith
    _ = B * (‖h a‖ + ‖h b‖ + (eVariationOn h (Icc a b)).toReal) + (B + M' * (b - a)) * ε₀ := by ring
    _ < B * (‖h a‖ + ‖h b‖ + (eVariationOn h (Icc a b)).toReal) + ε := by linarith

private lemma eVariationOn_inv_monotone_le {g : ℝ → ℝ} {a b lam : ℝ} (hab : a ≤ b) (hlam : 0 < lam)
    (hg_cont : ContinuousOn g (Icc a b))
    (hg_mono : MonotoneOn g (Icc a b) ∨ AntitoneOn g (Icc a b))
    (hg_lb : ∀ x ∈ Icc a b, lam ≤ |g x|) :
    eVariationOn (fun x => (g x)⁻¹) (Icc a b) ≤ ENNReal.ofReal lam⁻¹ := by
  have hsign : (∀ x ∈ Icc a b, lam ≤ g x) ∨ (∀ x ∈ Icc a b, g x ≤ -lam) := by
    have hne : ∀ x ∈ Icc a b, g x ≠ 0 := fun x hx h0 => by
      have := hg_lb x hx; rw [h0, abs_zero] at this; linarith
    rcases le_or_gt 0 (g a) with hga | hga
    · left
      intro x hx
      have hpos : 0 < g x := by
        by_contra hle
        have hle' : g x ≤ 0 := not_lt.mp hle
        have hga_pos : 0 < g a := lt_of_le_of_ne hga (hne a (left_mem_Icc.mpr hab)).symm
        obtain ⟨z, hz, hz0⟩ := intermediate_value_Icc' (hx.1) (hg_cont.mono (Icc_subset_Icc le_rfl hx.2))
          ⟨hle', hga_pos.le⟩
        exact hne z ⟨hz.1, hz.2.trans hx.2⟩ hz0
      have := hg_lb x hx
      rwa [abs_of_pos hpos] at this
    · right
      intro x hx
      have hneg : g x < 0 := by
        by_contra hge
        have hge' : 0 ≤ g x := not_lt.mp hge
        obtain ⟨z, hz, hz0⟩ := intermediate_value_Icc (hx.1) (hg_cont.mono (Icc_subset_Icc le_rfl hx.2))
          ⟨hga.le, hge'⟩
        exact hne z ⟨hz.1, hz.2.trans hx.2⟩ hz0
      have := hg_lb x hx
      rw [abs_of_neg hneg] at this
      linarith
  have h_inv_mono : MonotoneOn (fun x => (g x)⁻¹) (Icc a b) ∨
      AntitoneOn (fun x => (g x)⁻¹) (Icc a b) := by
    rcases hsign with hp | hn
    · rcases hg_mono with hm | ha
      · right; intro x hx y hy hxy; exact inv_anti₀ (lt_of_lt_of_le hlam (hp x hx)) (hm hx hy hxy)
      · left; intro x hx y hy hxy; exact inv_anti₀ (lt_of_lt_of_le hlam (hp y hy)) (ha hx hy hxy)
    · rcases hg_mono with hm | ha
      · right; intro x hx y hy hxy
        have hxg : g x < 0 := by linarith [hn x hx]
        have hyg : g y < 0 := by linarith [hn y hy]
        have hneg : -g y ≤ -g x := neg_le_neg (hm hx hy hxy)
        have hinv : (-g x)⁻¹ ≤ (-g y)⁻¹ := inv_anti₀ (by linarith) hneg
        simpa [inv_neg] using hinv
      · left; intro x hx y hy hxy
        have hxg : g x < 0 := by linarith [hn x hx]
        have hyg : g y < 0 := by linarith [hn y hy]
        have hneg : -g x ≤ -g y := neg_le_neg (ha hx hy hxy)
        have hinv : (-g y)⁻¹ ≤ (-g x)⁻¹ := inv_anti₀ (by linarith) hneg
        simpa [inv_neg] using hinv
  have hdiff_le : |(g b)⁻¹ - (g a)⁻¹| ≤ lam⁻¹ := by
    rcases hsign with hp | hn
    · have ha1 : 0 < (g a)⁻¹ := inv_pos.mpr (lt_of_lt_of_le hlam (hp a (left_mem_Icc.mpr hab)))
      have hb1 : 0 < (g b)⁻¹ := inv_pos.mpr (lt_of_lt_of_le hlam (hp b (right_mem_Icc.mpr hab)))
      have ha2 : (g a)⁻¹ ≤ lam⁻¹ := inv_anti₀ hlam (hp a (left_mem_Icc.mpr hab))
      have hb2 : (g b)⁻¹ ≤ lam⁻¹ := inv_anti₀ hlam (hp b (right_mem_Icc.mpr hab))
      rw [abs_sub_le_iff]
      constructor <;> linarith
    · have ha1 : (g a)⁻¹ < 0 := inv_lt_zero.mpr (by linarith [hn a (left_mem_Icc.mpr hab)])
      have hb1 : (g b)⁻¹ < 0 := inv_lt_zero.mpr (by linarith [hn b (right_mem_Icc.mpr hab)])
      have ha2 : -lam⁻¹ ≤ (g a)⁻¹ := by
        have := inv_anti₀ hlam (show lam ≤ -g a by linarith [hn a (left_mem_Icc.mpr hab)])
        rw [inv_neg] at this; linarith
      have hb2 : -lam⁻¹ ≤ (g b)⁻¹ := by
        have := inv_anti₀ hlam (show lam ≤ -g b by linarith [hn b (right_mem_Icc.mpr hab)])
        rw [inv_neg] at this; linarith
      rw [abs_sub_le_iff]
      constructor <;> linarith
  rcases h_inv_mono with hm | ha
  · have hev := hm.eVariationOn_eq (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab)
    rw [inter_self] at hev
    rw [hev]
    exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans hdiff_le)
  · have hm : MonotoneOn (fun x => -((g x)⁻¹)) (Icc a b) := fun x hx y hy hxy => neg_le_neg (ha hx hy hxy)
    have hev : eVariationOn (fun x => (g x)⁻¹) (Icc a b) = eVariationOn (fun x => -((g x)⁻¹)) (Icc a b) := by
      simp only [eVariationOn, edist_neg_neg]
    have hev2 := hm.eVariationOn_eq (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab)
    rw [inter_self] at hev2
    rw [hev, hev2]
    simp only [neg_sub_neg]
    exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (by rw [abs_sub_comm]; exact hdiff_le))

/-- First-derivative van der Corput estimate (coordinate-changed form). -/
theorem van_der_corput_first_comp {a b c lam M : ℝ} (hab : a ≤ b) (hc : 0 < c) (hlam : 0 < lam)
    {w w' : ℝ → ℝ} (hw : ∀ x ∈ Icc a b, HasDerivAt w (w' x) x)
    (hw_cont : ContinuousOn w' (Icc a b)) (hw_nn : ∀ x ∈ Icc a b, 0 ≤ w' x)
    {φ φ' : ℝ → ℝ} (hφ : ∀ y ∈ Icc (w a) (w b), HasDerivAt φ (φ' y) y)
    (hφ'_cont : ContinuousOn φ' (Icc (w a) (w b)))
    (hφ'_mono : MonotoneOn φ' (Icc (w a) (w b)) ∨ AntitoneOn φ' (Icc (w a) (w b)))
    (hφ'_lb : ∀ x ∈ Icc a b, lam ≤ |φ' (w x)|)
    {h : ℝ → ℂ} (hh_cont : ContinuousOn h (Icc a b)) (hh_bv : BoundedVariationOn h (Icc a b))
    (hh_bound : ∀ x ∈ Icc a b, ‖h x‖ ≤ M) :
    ‖∫ x in a..b, h x * (w' x : ℂ) * Complex.exp (Complex.I * (c : ℂ) * (φ (w x) : ℂ))‖ ≤
      3 * (M + (eVariationOn h (Icc a b)).toReal) / (c * lam) := by
  have hM_nn : 0 ≤ M := (norm_nonneg (h a)).trans (hh_bound a (left_mem_Icc.mpr hab))
  have hw_mono : MonotoneOn w (Icc a b) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc a b)
      (fun x hx => (hw x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hw x (interior_subset hx)).differentiableAt.differentiableWithinAt) ?_
    intro x hx
    rw [interior_Icc] at hx
    have hxi : x ∈ Icc a b := Ioo_subset_Icc_self hx
    rw [(hw x hxi).deriv]
    exact hw_nn x hxi
  have hw_maps : MapsTo w (Icc a b) (Icc (w a) (w b)) := fun x hx =>
    ⟨hw_mono (left_mem_Icc.mpr hab) hx hx.1, hw_mono hx (right_mem_Icc.mpr hab) hx.2⟩
  have hw_cont' : ContinuousOn w (Icc a b) := fun x hx => (hw x hx).continuousAt.continuousWithinAt
  set g : ℝ → ℝ := fun x => (φ' (w x))⁻¹
  have hg_mono : MonotoneOn (φ' ∘ w) (Icc a b) ∨ AntitoneOn (φ' ∘ w) (Icc a b) := by
    rcases hφ'_mono with hm | ha
    · left; exact fun x hx y hy hxy => hm (hw_maps hx) (hw_maps hy) (hw_mono hx hy hxy)
    · right; exact fun x hx y hy hxy => ha (hw_maps hx) (hw_maps hy) (hw_mono hx hy hxy)
  have hg_cont : ContinuousOn (φ' ∘ w) (Icc a b) := hφ'_cont.comp hw_cont' hw_maps
  have hg_bv_le : eVariationOn g (Icc a b) ≤ ENNReal.ofReal lam⁻¹ :=
    eVariationOn_inv_monotone_le hab hlam hg_cont hg_mono hφ'_lb
  have hg_bv : BoundedVariationOn g (Icc a b) :=
    ne_top_of_le_ne_top ENNReal.ofReal_lt_top.ne hg_bv_le
  have hg_bound : ∀ x ∈ Icc a b, ‖g x‖ ≤ lam⁻¹ := fun x hx => by
    rw [Real.norm_eq_abs, abs_inv]
    exact inv_anti₀ hlam (hφ'_lb x hx)
  have hg_cont_inv : ContinuousOn g (Icc a b) :=
    hg_cont.inv₀ fun x hx h0 => by
      dsimp only [Function.comp_apply] at h0
      have := hφ'_lb x hx; rw [h0, abs_zero] at this; linarith
  let u : ℝ → ℂ := fun x => ((Complex.I * (c : ℂ))⁻¹ * (g x : ℂ)) * h x
  have hu_cont : ContinuousOn u (Icc a b) :=
    (continuousOn_const.mul (Complex.continuous_ofReal.continuousOn.comp hg_cont_inv (mapsTo_univ _ _))).mul
      hh_cont
  have hu_bv_le : eVariationOn u (Icc a b) ≤
      ENNReal.ofReal (c⁻¹ * (lam⁻¹ * (eVariationOn h (Icc a b)).toReal + M * lam⁻¹)) := by
    have hsmul : eVariationOn (fun x => g x • h x) (Icc a b) ≤
        ENNReal.ofReal lam⁻¹ * eVariationOn h (Icc a b) + ENNReal.ofReal M * eVariationOn g (Icc a b) := by
      refine eVariationOn_fun_smul_le (fun x hx => ?_) (fun x hx => ?_)
      · rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_le_ofReal (by simpa [Real.norm_eq_abs] using hg_bound x hx)
      · rw [enorm_eq_nnnorm, ← ENNReal.ofReal_coe_nnreal]; exact ENNReal.ofReal_le_ofReal (hh_bound x hx)
    have hsmul_ub : eVariationOn (fun x => g x • h x) (Icc a b) ≤
        ENNReal.ofReal lam⁻¹ * eVariationOn h (Icc a b) + ENNReal.ofReal M * ENNReal.ofReal lam⁻¹ :=
      hsmul.trans (by gcongr)
    have hsmul' : eVariationOn (fun x => g x • h x) (Icc a b) ≤
        ENNReal.ofReal (lam⁻¹ * (eVariationOn h (Icc a b)).toReal + M * lam⁻¹) := by
      refine hsmul_ub.trans_eq ?_
      calc ENNReal.ofReal lam⁻¹ * eVariationOn h (Icc a b) + ENNReal.ofReal M * ENNReal.ofReal lam⁻¹
          = ENNReal.ofReal lam⁻¹ * ENNReal.ofReal (eVariationOn h (Icc a b)).toReal +
              ENNReal.ofReal M * ENNReal.ofReal lam⁻¹ := by
            conv_lhs => rw [← ENNReal.ofReal_toReal hh_bv]
        _ = ENNReal.ofReal (lam⁻¹ * (eVariationOn h (Icc a b)).toReal + M * lam⁻¹) := by
            rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hM_nn,
              ← ENNReal.ofReal_add (by positivity) (by positivity)]
    have hueq : ∀ t, u t = (Complex.I * (c : ℂ))⁻¹ * (g t • h t) := fun t => by
      simp [u, Complex.real_smul, mul_assoc]
    have hconst : eVariationOn u (Icc a b) ≤
        ENNReal.ofReal c⁻¹ * eVariationOn (fun x => g x • h x) (Icc a b) := by
      apply iSup_le
      rintro ⟨n, seq, hseq, hmem⟩
      calc ∑ i ∈ Finset.range n, edist (u (seq (i + 1))) (u (seq i))
          = ∑ i ∈ Finset.range n, ENNReal.ofReal c⁻¹ *
              edist (g (seq (i + 1)) • h (seq (i + 1))) (g (seq i) • h (seq i)) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [hueq, hueq, edist_dist, edist_dist, dist_eq_norm, dist_eq_norm, ← mul_sub,
              norm_mul, norm_inv, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
              Real.norm_eq_abs, abs_of_pos hc, ENNReal.ofReal_mul (by positivity)]
        _ = ENNReal.ofReal c⁻¹ *
              ∑ i ∈ Finset.range n, edist (g (seq (i + 1)) • h (seq (i + 1))) (g (seq i) • h (seq i)) := by
            rw [← Finset.mul_sum]
        _ ≤ ENNReal.ofReal c⁻¹ * eVariationOn (fun x => g x • h x) (Icc a b) :=
            mul_le_mul_of_nonneg_left
              (eVariationOn.sum_le (f := fun x => g x • h x) (s := Icc a b) hseq hmem) bot_le
    calc eVariationOn u (Icc a b)
        ≤ ENNReal.ofReal c⁻¹ * eVariationOn (fun x => g x • h x) (Icc a b) := hconst
      _ ≤ ENNReal.ofReal c⁻¹ *
            ENNReal.ofReal (lam⁻¹ * (eVariationOn h (Icc a b)).toReal + M * lam⁻¹) := by
          gcongr
      _ = ENNReal.ofReal (c⁻¹ * (lam⁻¹ * (eVariationOn h (Icc a b)).toReal + M * lam⁻¹)) := by
          rw [ENNReal.ofReal_mul (by positivity)]
  have hu_bv : BoundedVariationOn u (Icc a b) :=
    ne_top_of_le_ne_top ENNReal.ofReal_lt_top.ne hu_bv_le
  let F : ℝ → ℂ := fun x => Complex.exp (Complex.I * (c : ℂ) * (φ (w x) : ℂ))
  let F' : ℝ → ℂ := fun x =>
    (Complex.I * (c : ℂ) * (φ' (w x) : ℂ) * (w' x : ℂ)) * F x
  have hF : ∀ x ∈ Icc a b, HasDerivAt F (F' x) x := fun x hx => by
    have hcomp : HasDerivAt (fun t => φ (w t)) (φ' (w x) * w' x) x :=
      HasDerivAt.comp x (hφ (w x) (hw_maps hx)) (hw x hx)
    have hc_mul : HasDerivAt (fun t => Complex.I * (c : ℂ) * (φ (w t) : ℂ))
        (Complex.I * (c : ℂ) * ((φ' (w x) * w' x : ℝ) : ℂ)) x :=
      (HasDerivAt.ofReal_comp hcomp).const_mul (Complex.I * (c : ℂ))
    refine (HasDerivAt.cexp hc_mul).congr_deriv ?_
    dsimp [F', F]
    push_cast
    ring
  have hF'_cont : ContinuousOn F' (Icc a b) := by
    have h1 : ContinuousOn (fun x => Complex.I * (c : ℂ) * (φ' (w x) : ℂ) * (w' x : ℂ)) (Icc a b) :=
      ((continuousOn_const.mul (Complex.continuous_ofReal.continuousOn.comp hg_cont (mapsTo_univ _ _))).mul
        (Complex.continuous_ofReal.continuousOn.comp hw_cont (mapsTo_univ _ _)))
    have h2 : ContinuousOn F (Icc a b) := by
      have hφ_cont : ContinuousOn φ (Icc (w a) (w b)) := fun y hy => (hφ y hy).continuousAt.continuousWithinAt
      exact Complex.continuous_exp.continuousOn.comp
        (continuousOn_const.mul (Complex.continuous_ofReal.continuousOn.comp
          (hφ_cont.comp hw_cont' hw_maps) (mapsTo_univ _ _))) (mapsTo_univ _ _)
    exact h1.mul h2
  have hF_bound : ∀ x ∈ Icc a b, ‖F x‖ ≤ 1 := fun x _ => by
    dsimp [F]
    rw [show Complex.I * (c : ℂ) * (φ (w x) : ℂ) = ((c * φ (w x) : ℝ) : ℂ) * Complex.I by
      push_cast; ring, Complex.norm_exp_ofReal_mul_I]
  have h_eq : EqOn (fun x => h x * (w' x : ℂ) * F x) (fun x => u x * F' x) (Icc a b) := by
    intro x hx
    have hφ'_ne : (φ' (w x) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by
      intro h0; have := hφ'_lb x hx; rw [h0, abs_zero] at this; linarith)
    have hc_ne : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
    dsimp [u, g, F']
    push_cast
    field_simp [Complex.I_ne_zero, hc_ne, hφ'_ne]
  have hint_eq : ∫ x in a..b, h x * (w' x : ℂ) * F x = ∫ x in a..b, u x * F' x :=
    intervalIntegral.integral_congr (by rw [uIcc_of_le hab]; exact h_eq)
  have h_ibp := norm_integral_mul_deriv_le_of_boundedVariation hab hu_cont hu_bv hF hF'_cont
    zero_le_one hF_bound
  have hu_end : ∀ x ∈ Icc a b, ‖u x‖ ≤ M / (c * lam) := fun x hx => by
    dsimp [u]
    rw [norm_mul, norm_mul, norm_inv, norm_mul, Complex.norm_I, one_mul,
      Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
    have hgx : |g x| ≤ lam⁻¹ := by
      simpa [Real.norm_eq_abs] using hg_bound x hx
    calc c⁻¹ * |g x| * ‖h x‖ ≤ c⁻¹ * lam⁻¹ * M := by gcongr; exact hh_bound x hx
      _ = M / (c * lam) := by ring
  have htv_real : (eVariationOn u (Icc a b)).toReal ≤
      c⁻¹ * (lam⁻¹ * (eVariationOn h (Icc a b)).toReal + M * lam⁻¹) :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hu_bv_le
  rw [hint_eq]
  calc ‖∫ x in a..b, u x * F' x‖
      ≤ 1 * (‖u a‖ + ‖u b‖ + (eVariationOn u (Icc a b)).toReal) := h_ibp
    _ ≤ 1 * (M / (c * lam) + M / (c * lam) +
          c⁻¹ * (lam⁻¹ * (eVariationOn h (Icc a b)).toReal + M * lam⁻¹)) := by
        gcongr
        · exact hu_end a (left_mem_Icc.mpr hab)
        · exact hu_end b (right_mem_Icc.mpr hab)
    _ = (3 * M + (eVariationOn h (Icc a b)).toReal) / (c * lam) := by ring
    _ ≤ 3 * (M + (eVariationOn h (Icc a b)).toReal) / (c * lam) := by
        have : 0 ≤ (eVariationOn h (Icc a b)).toReal := ENNReal.toReal_nonneg
        gcongr; linarith

/-- First-derivative van der Corput estimate (standard `w = id` form). -/
theorem van_der_corput_first {a b c lam M : ℝ} (hab : a ≤ b) (hc : 0 < c) (hlam : 0 < lam)
    {φ φ' : ℝ → ℝ} (hφ : ∀ y ∈ Icc a b, HasDerivAt φ (φ' y) y)
    (hφ'_cont : ContinuousOn φ' (Icc a b))
    (hφ'_mono : MonotoneOn φ' (Icc a b) ∨ AntitoneOn φ' (Icc a b))
    (hφ'_lb : ∀ x ∈ Icc a b, lam ≤ |φ' x|)
    {h : ℝ → ℂ} (hh_cont : ContinuousOn h (Icc a b)) (hh_bv : BoundedVariationOn h (Icc a b))
    (hh_bound : ∀ x ∈ Icc a b, ‖h x‖ ≤ M) :
    ‖∫ x in a..b, h x * Complex.exp (Complex.I * (c : ℂ) * (φ x : ℂ))‖ ≤
      3 * (M + (eVariationOn h (Icc a b)).toReal) / (c * lam) := by
  have h1 := van_der_corput_first_comp hab hc hlam (w := id) (w' := fun _ => 1)
    (fun x _ => hasDerivAt_id x) continuousOn_const (fun _ _ => zero_le_one)
    hφ hφ'_cont hφ'_mono hφ'_lb hh_cont hh_bv hh_bound
  simpa only [id, Complex.ofReal_one, mul_one] using h1

private lemma slope_lb_of_second_deriv {φ' φ'' : ℝ → ℝ} {A B lam : ℝ} (hAB : A ≤ B)
    (hφ' : ∀ y ∈ Icc A B, HasDerivAt φ' (φ'' y) y)
    (hφ''_lb : ∀ y ∈ Icc A B, lam ≤ |φ'' y|)
    {y₁ y₂ : ℝ} (hy₁ : y₁ ∈ Icc A B) (hy₂ : y₂ ∈ Icc A B) :
    lam * |y₁ - y₂| ≤ |φ' y₁ - φ' y₂| := by
  wlog h12 : y₁ ≤ y₂
  · rw [abs_sub_comm y₁ y₂, abs_sub_comm (φ' y₁) (φ' y₂)]
    exact this hAB hφ' hφ''_lb hy₂ hy₁ (le_of_not_ge h12)
  rcases eq_or_lt_of_le h12 with rfl | hlt
  · simp
  obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope φ' φ'' hlt
    (fun y hy => (hφ' y ⟨hy₁.1.trans hy.1, hy.2.trans hy₂.2⟩).continuousAt.continuousWithinAt)
    (fun y hy => hφ' y ⟨hy₁.1.trans hy.1.le, hy.2.le.trans hy₂.2⟩)
  have hξ_mem : ξ ∈ Icc A B := ⟨hy₁.1.trans hξ.1.le, hξ.2.le.trans hy₂.2⟩
  have heq : φ' y₂ - φ' y₁ = φ'' ξ * (y₂ - y₁) := by
    rw [eq_div_iff (sub_pos.mpr hlt).ne'] at hslope
    linarith
  rw [abs_sub_comm y₁ y₂, abs_sub_comm (φ' y₁) (φ' y₂), heq, abs_mul,
    abs_of_pos (sub_pos.mpr hlt)]
  exact mul_le_mul_of_nonneg_right (hφ''_lb ξ hξ_mem) (sub_nonneg.mpr hlt.le)

/-- Second-derivative van der Corput estimate (coordinate-changed form). -/
theorem van_der_corput_second_comp {a b c lam M : ℝ} (hab : a ≤ b) (hc : 0 < c) (hlam : 0 < lam)
    {w w' : ℝ → ℝ} (hw : ∀ x ∈ Icc a b, HasDerivAt w (w' x) x)
    (hw_cont : ContinuousOn w' (Icc a b)) (hw_nn : ∀ x ∈ Icc a b, 0 ≤ w' x)
    {φ φ' φ'' : ℝ → ℝ} (hφ : ∀ y ∈ Icc (w a) (w b), HasDerivAt φ (φ' y) y)
    (hφ' : ∀ y ∈ Icc (w a) (w b), HasDerivAt φ' (φ'' y) y)
    (hφ'_mono : MonotoneOn φ' (Icc (w a) (w b)) ∨ AntitoneOn φ' (Icc (w a) (w b)))
    (hφ''_lb : ∀ y ∈ Icc (w a) (w b), lam ≤ |φ'' y|)
    {h : ℝ → ℂ} (hh_cont : ContinuousOn h (Icc a b)) (hh_bv : BoundedVariationOn h (Icc a b))
    (hh_bound : ∀ x ∈ Icc a b, ‖h x‖ ≤ M) :
    ‖∫ x in a..b, h x * (w' x : ℂ) * Complex.exp (Complex.I * (c : ℂ) * (φ (w x) : ℂ))‖ ≤
      8 * (M + (eVariationOn h (Icc a b)).toReal) / √(c * lam) := by
  have hM_nn : 0 ≤ M := (norm_nonneg (h a)).trans (hh_bound a (left_mem_Icc.mpr hab))
  have hsqrt_pos : 0 < √(c * lam) := Real.sqrt_pos.mpr (mul_pos hc hlam)
  have hw_mono : MonotoneOn w (Icc a b) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc a b)
      (fun x hx => (hw x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hw x (interior_subset hx)).differentiableAt.differentiableWithinAt) ?_
    intro x hx
    rw [interior_Icc] at hx
    have hxi : x ∈ Icc a b := Ioo_subset_Icc_self hx
    rw [(hw x hxi).deriv]
    exact hw_nn x hxi
  have hw_maps : MapsTo w (Icc a b) (Icc (w a) (w b)) := fun x hx =>
    ⟨hw_mono (left_mem_Icc.mpr hab) hx hx.1, hw_mono hx (right_mem_Icc.mpr hab) hx.2⟩
  have hw_cont' : ContinuousOn w (Icc a b) := fun x hx => (hw x hx).continuousAt.continuousWithinAt
  have hφ'_cont : ContinuousOn φ' (Icc (w a) (w b)) :=
    fun y hy => (hφ' y hy).continuousAt.continuousWithinAt
  have hφ_cont : ContinuousOn φ (Icc (w a) (w b)) :=
    fun y hy => (hφ y hy).continuousAt.continuousWithinAt
  have hcomp_cont : ContinuousOn (fun x => |φ' (w x)|) (Icc a b) :=
    (hφ'_cont.comp hw_cont' hw_maps).abs
  obtain ⟨xstar, hxstar_mem, hxstar_min⟩ :=
    isCompact_Icc.exists_isMinOn ⟨a, left_mem_Icc.mpr hab⟩ hcomp_cont
  have h_dist_lb : ∀ x ∈ Icc a b, lam * |w x - w xstar| ≤ |φ' (w x)| := by
    have hslope : ∀ x ∈ Icc a b, lam * |w x - w xstar| ≤ |φ' (w x) - φ' (w xstar)| := fun x hx =>
      slope_lb_of_second_deriv (hw_mono (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab) hab)
        hφ' hφ''_lb (hw_maps hx) (hw_maps hxstar_mem)
    by_cases hzero : φ' (w xstar) = 0
    · intro x hx; simpa [hzero] using hslope x hx
    · have hne : ∀ x ∈ Icc a b, φ' (w x) ≠ 0 := fun x hx h0 => by
        have hle_min : |φ' (w xstar)| ≤ |φ' (w x)| := isMinOn_iff.mp hxstar_min x hx
        rw [h0, abs_zero] at hle_min
        exact hzero (abs_eq_zero.mp (le_antisymm hle_min (abs_nonneg _)))
      have hsign : (∀ x ∈ Icc a b, 0 < φ' (w x)) ∨ (∀ x ∈ Icc a b, φ' (w x) < 0) := by
        rcases lt_or_gt_of_ne hzero with hneg | hpos
        · right
          intro x hx
          by_contra hge
          have hge' : 0 ≤ φ' (w x) := not_lt.mp hge
          have hc_comp : ContinuousOn (fun t => φ' (w t)) (Icc a b) := hφ'_cont.comp hw_cont' hw_maps
          rcases le_total x xstar with hxx | hxx
          · obtain ⟨z, hz, hz0⟩ := intermediate_value_Icc' hxx
              (hc_comp.mono (Icc_subset_Icc hx.1 hxstar_mem.2)) ⟨hneg.le, hge'⟩
            exact hne z ⟨hx.1.trans hz.1, hz.2.trans hxstar_mem.2⟩ hz0
          · obtain ⟨z, hz, hz0⟩ := intermediate_value_Icc hxx
              (hc_comp.mono (Icc_subset_Icc hxstar_mem.1 hx.2)) ⟨hneg.le, hge'⟩
            exact hne z ⟨hxstar_mem.1.trans hz.1, hz.2.trans hx.2⟩ hz0
        · left
          intro x hx
          by_contra hle
          have hle' : φ' (w x) ≤ 0 := not_lt.mp hle
          have hc_comp : ContinuousOn (fun t => φ' (w t)) (Icc a b) := hφ'_cont.comp hw_cont' hw_maps
          rcases le_total x xstar with hxx | hxx
          · obtain ⟨z, hz, hz0⟩ := intermediate_value_Icc hxx
              (hc_comp.mono (Icc_subset_Icc hx.1 hxstar_mem.2)) ⟨hle', hpos.le⟩
            exact hne z ⟨hx.1.trans hz.1, hz.2.trans hxstar_mem.2⟩ hz0
          · obtain ⟨z, hz, hz0⟩ := intermediate_value_Icc' hxx
              (hc_comp.mono (Icc_subset_Icc hxstar_mem.1 hx.2)) ⟨hle', hpos.le⟩
            exact hne z ⟨hxstar_mem.1.trans hz.1, hz.2.trans hx.2⟩ hz0
      intro x hx
      have hmin : |φ' (w xstar)| ≤ |φ' (w x)| := isMinOn_iff.mp hxstar_min x hx
      rcases hsign with hp | hn
      · have hle : φ' (w xstar) ≤ φ' (w x) := by
          rwa [abs_of_pos (hp xstar hxstar_mem), abs_of_pos (hp x hx)] at hmin
        calc lam * |w x - w xstar| ≤ |φ' (w x) - φ' (w xstar)| := hslope x hx
          _ = φ' (w x) - φ' (w xstar) := abs_of_nonneg (by linarith)
          _ ≤ φ' (w x) := by linarith [hp xstar hxstar_mem]
          _ = |φ' (w x)| := (abs_of_pos (hp x hx)).symm
      · have hle : φ' (w x) ≤ φ' (w xstar) := by
          rw [abs_of_neg (hn xstar hxstar_mem), abs_of_neg (hn x hx)] at hmin
          linarith
        calc lam * |w x - w xstar| ≤ |φ' (w x) - φ' (w xstar)| := hslope x hx
          _ = φ' (w xstar) - φ' (w x) := by rw [abs_sub_comm]; exact abs_of_nonneg (by linarith)
          _ ≤ -φ' (w x) := by linarith [hn xstar hxstar_mem]
          _ = |φ' (w x)| := (abs_of_neg (hn x hx)).symm
  set δ := (√(c * lam))⁻¹
  have hδ_pos : 0 < δ := inv_pos.mpr hsqrt_pos
  have ha'_ex : ∃ a' ∈ Icc a xstar, (a' = a ∧ w xstar - w a ≤ δ) ∨ (w a' = w xstar - δ) := by
    rcases le_or_gt (w xstar - w a) δ with hle | hgt
    · exact ⟨a, left_mem_Icc.mpr hxstar_mem.1, Or.inl ⟨rfl, hle⟩⟩
    · have ha' : w a ≤ w xstar - δ ∧ w xstar - δ ≤ w xstar := ⟨by linarith, by linarith⟩
      obtain ⟨a', ha'_mem, ha'_eq⟩ := intermediate_value_Icc hxstar_mem.1
        (hw_cont'.mono (Icc_subset_Icc (left_mem_Icc.mpr hab).1 hxstar_mem.2)) ha'
      exact ⟨a', ha'_mem, Or.inr ha'_eq⟩
  obtain ⟨a', ha'_mem, ha'_prop⟩ := ha'_ex
  have hb'_ex : ∃ b' ∈ Icc xstar b, (b' = b ∧ w b - w xstar ≤ δ) ∨ (w b' = w xstar + δ) := by
    rcases le_or_gt (w b - w xstar) δ with hle | hgt
    · exact ⟨b, right_mem_Icc.mpr hxstar_mem.2, Or.inl ⟨rfl, hle⟩⟩
    · have hb' : w xstar ≤ w xstar + δ ∧ w xstar + δ ≤ w b := ⟨by linarith, by linarith⟩
      obtain ⟨b', hb'_mem, hb'_eq⟩ := intermediate_value_Icc hxstar_mem.2
        (hw_cont'.mono (Icc_subset_Icc hxstar_mem.1 (right_mem_Icc.mpr hab).2)) hb'
      exact ⟨b', hb'_mem, Or.inr hb'_eq⟩
  obtain ⟨b', hb'_mem, hb'_prop⟩ := hb'_ex
  let F_osc : ℝ → ℂ := fun x =>
    h x * (w' x : ℂ) * Complex.exp (Complex.I * (c : ℂ) * (φ (w x) : ℂ))
  have hF_osc_int : IntervalIntegrable F_osc volume a b := by
    have hcont : ContinuousOn F_osc (Icc a b) := by
      refine (hh_cont.mul (Complex.continuous_ofReal.continuousOn.comp hw_cont (mapsTo_univ _ _))).mul ?_
      exact Complex.continuous_exp.continuousOn.comp
        (continuousOn_const.mul (Complex.continuous_ofReal.continuousOn.comp
          (hφ_cont.comp hw_cont' hw_maps) (mapsTo_univ _ _))) (mapsTo_univ _ _)
    exact hcont.intervalIntegrable_of_Icc hab
  have ha'_le_b' : a' ≤ b' := ha'_mem.2.trans hb'_mem.1
  have h_split : ∫ x in a..b, F_osc x =
      (∫ x in a..a', F_osc x) + (∫ x in a'..b', F_osc x) + (∫ x in b'..b, F_osc x) := by
    have h1 := intervalIntegral.integral_add_adjacent_intervals
      (hF_osc_int.mono_set (uIcc_subset_uIcc (by rw [uIcc_of_le hab]; exact left_mem_Icc.mpr hab)
        (by rw [uIcc_of_le hab]; exact ⟨ha'_mem.1, ha'_mem.2.trans hxstar_mem.2⟩)))
      (hF_osc_int.mono_set (uIcc_subset_uIcc
        (by rw [uIcc_of_le hab]; exact ⟨ha'_mem.1, ha'_mem.2.trans hxstar_mem.2⟩)
        (by rw [uIcc_of_le hab]; exact ⟨hb'_mem.1.trans' hxstar_mem.1, hb'_mem.2⟩)))
    have h2 := intervalIntegral.integral_add_adjacent_intervals
      (hF_osc_int.mono_set (uIcc_subset_uIcc (by rw [uIcc_of_le hab]; exact left_mem_Icc.mpr hab)
        (by rw [uIcc_of_le hab]; exact ⟨hb'_mem.1.trans' hxstar_mem.1, hb'_mem.2⟩)))
      (hF_osc_int.mono_set (uIcc_subset_uIcc
        (by rw [uIcc_of_le hab]; exact ⟨hb'_mem.1.trans' hxstar_mem.1, hb'_mem.2⟩)
        (by rw [uIcc_of_le hab]; exact right_mem_Icc.mpr hab)))
    rw [← h2, ← h1]
  have h_mid : ‖∫ x in a'..b', F_osc x‖ ≤ 2 * M / √(c * lam) := by
    have h_ub : ∀ x ∈ Ioc a' b', ‖F_osc x‖ ≤ M * w' x := fun x hx => by
      have hx_ab : x ∈ Icc a b := ⟨ha'_mem.1.trans hx.1.le, hx.2.trans hb'_mem.2⟩
      dsimp [F_osc]
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw_nn x hx_ab),
        show Complex.I * (c : ℂ) * (φ (w x) : ℂ) = ((c * φ (w x) : ℝ) : ℂ) * Complex.I by
          push_cast; ring, Complex.norm_exp_ofReal_mul_I, mul_one]
      exact mul_le_mul_of_nonneg_right (hh_bound x hx_ab) (hw_nn x hx_ab)
    have h_int_w : ∫ x in a'..b', M * w' x = M * (w b' - w a') := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun x hx => hw x ⟨ha'_mem.1.trans (uIcc_of_le ha'_le_b' ▸ hx).1,
            (uIcc_of_le ha'_le_b' ▸ hx).2.trans hb'_mem.2⟩)
          ((hw_cont.mono (Icc_subset_Icc ha'_mem.1 hb'_mem.2)).intervalIntegrable_of_Icc ha'_le_b')]
    have hw_diff : w b' - w a' ≤ 2 * δ := by
      have hwa : w xstar - w a' ≤ δ := by
        rcases ha'_prop with ⟨rfl, hle⟩ | heq
        · exact hle
        · linarith
      have hwb : w b' - w xstar ≤ δ := by
        rcases hb'_prop with ⟨rfl, hle⟩ | heq
        · exact hle
        · linarith
      linarith
    have hw'_cont : ContinuousOn (fun x => M * w' x) (Icc a' b') :=
      continuousOn_const.mul (hw_cont.mono (Icc_subset_Icc ha'_mem.1 hb'_mem.2))
    have h_norm : ‖∫ x in a'..b', F_osc x‖ ≤ ∫ x in a'..b', M * w' x :=
      intervalIntegral.norm_integral_le_of_norm_le ha'_le_b'
        (Eventually.of_forall fun x hx => h_ub x hx)
        (hw'_cont.intervalIntegrable_of_Icc ha'_le_b')
    calc ‖∫ x in a'..b', F_osc x‖
        ≤ ∫ x in a'..b', M * w' x := h_norm
      _ = M * (w b' - w a') := h_int_w
      _ ≤ M * (2 * δ) := mul_le_mul_of_nonneg_left hw_diff hM_nn
      _ = 2 * M / √(c * lam) := by dsimp [δ]; ring
  have h_left : ‖∫ x in a..a', F_osc x‖ ≤
      3 * (M + (eVariationOn h (Icc a a')).toReal) / √(c * lam) := by
    rcases ha'_prop with ⟨rfl, _⟩ | ha'_eq
    · simp only [intervalIntegral.integral_same, norm_zero]
      positivity
    · have hsub_aa' : Icc a a' ⊆ Icc a b := Icc_subset_Icc le_rfl (ha'_mem.2.trans hxstar_mem.2)
      have hsub_waa' : Icc (w a) (w a') ⊆ Icc (w a) (w b) :=
        Icc_subset_Icc le_rfl (hw_mono (ha'_mem.2.trans hxstar_mem.2 |> fun h => ⟨ha'_mem.1, h⟩)
          (right_mem_Icc.mpr hab) (ha'_mem.2.trans hxstar_mem.2))
      have hlam_left : ∀ x ∈ Icc a a', lam * δ ≤ |φ' (w x)| := fun x hx => by
        have hx_ab : x ∈ Icc a b := hsub_aa' hx
        have hwx_le : w x ≤ w a' := hw_mono hx_ab ⟨ha'_mem.1, ha'_mem.2.trans hxstar_mem.2⟩ hx.2
        have h_abs : δ ≤ |w x - w xstar| := by
          rw [abs_of_nonpos (by linarith)]
          linarith
        exact (mul_le_mul_of_nonneg_left h_abs hlam.le).trans (h_dist_lb x hx_ab)
      have h_vdc := van_der_corput_first_comp ha'_mem.1 hc (mul_pos hlam hδ_pos)
        (fun x hx => hw x (hsub_aa' hx)) (hw_cont.mono hsub_aa') (fun x hx => hw_nn x (hsub_aa' hx))
        (fun y hy => hφ y (hsub_waa' hy)) (hφ'_cont.mono hsub_waa')
        (Or.elim hφ'_mono (fun hm => Or.inl (hm.mono hsub_waa'))
          (fun ha => Or.inr (ha.mono hsub_waa')))
        hlam_left (hh_cont.mono hsub_aa') (hh_bv.mono hsub_aa') (fun x hx => hh_bound x (hsub_aa' hx))
      have h_den_eq : c * (lam * δ) = √(c * lam) := by
        dsimp [δ]
        have : √(c * lam) ^ 2 = c * lam := Real.sq_sqrt (mul_pos hc hlam).le
        field_simp [hsqrt_pos.ne']
        linarith
      rwa [h_den_eq] at h_vdc
  have h_right : ‖∫ x in b'..b, F_osc x‖ ≤
      3 * (M + (eVariationOn h (Icc b' b)).toReal) / √(c * lam) := by
    rcases hb'_prop with ⟨rfl, _⟩ | hb'_eq
    · simp only [intervalIntegral.integral_same, norm_zero]
      positivity
    · have hsub_b'b : Icc b' b ⊆ Icc a b := Icc_subset_Icc (hxstar_mem.1.trans hb'_mem.1) le_rfl
      have hsub_wb'b : Icc (w b') (w b) ⊆ Icc (w a) (w b) :=
        Icc_subset_Icc (hw_mono (left_mem_Icc.mpr hab) ⟨hxstar_mem.1.trans hb'_mem.1, hb'_mem.2⟩
          (hxstar_mem.1.trans hb'_mem.1)) le_rfl
      have hlam_right : ∀ x ∈ Icc b' b, lam * δ ≤ |φ' (w x)| := fun x hx => by
        have hx_ab : x ∈ Icc a b := hsub_b'b hx
        have hwb'_le : w b' ≤ w x := hw_mono ⟨hxstar_mem.1.trans hb'_mem.1, hb'_mem.2⟩ hx_ab hx.1
        have h_abs : δ ≤ |w x - w xstar| := by
          rw [abs_of_nonneg (by linarith)]
          linarith
        exact (mul_le_mul_of_nonneg_left h_abs hlam.le).trans (h_dist_lb x hx_ab)
      have h_vdc := van_der_corput_first_comp hb'_mem.2 hc (mul_pos hlam hδ_pos)
        (fun x hx => hw x (hsub_b'b hx)) (hw_cont.mono hsub_b'b) (fun x hx => hw_nn x (hsub_b'b hx))
        (fun y hy => hφ y (hsub_wb'b hy)) (hφ'_cont.mono hsub_wb'b)
        (Or.elim hφ'_mono (fun hm => Or.inl (hm.mono hsub_wb'b))
          (fun ha => Or.inr (ha.mono hsub_wb'b)))
        hlam_right (hh_cont.mono hsub_b'b) (hh_bv.mono hsub_b'b) (fun x hx => hh_bound x (hsub_b'b hx))
      have h_den_eq : c * (lam * δ) = √(c * lam) := by
        dsimp [δ]
        have : √(c * lam) ^ 2 = c * lam := Real.sq_sqrt (mul_pos hc hlam).le
        field_simp [hsqrt_pos.ne']
        linarith
      rwa [h_den_eq] at h_vdc
  have h_tv_sum : (eVariationOn h (Icc a a')).toReal + (eVariationOn h (Icc b' b)).toReal ≤
      (eVariationOn h (Icc a b)).toReal := by
    have h_add : eVariationOn h (Icc a a') + eVariationOn h (Icc b' b) ≤ eVariationOn h (Icc a b) := by
      have haa'b : a' ≤ b := ha'_mem.2.trans hb'_mem.1 |>.trans hb'_mem.2
      have h1' := eVariationOn.Icc_add_Icc h ha'_mem.1 haa'b (mem_univ a')
      simp only [univ_inter] at h1'
      have h2' : eVariationOn h (Icc b' b) ≤ eVariationOn h (Icc a' b) :=
        eVariationOn.mono h (Icc_subset_Icc ha'_le_b' le_rfl)
      calc eVariationOn h (Icc a a') + eVariationOn h (Icc b' b)
          ≤ eVariationOn h (Icc a a') + eVariationOn h (Icc a' b) := add_le_add le_rfl h2'
        _ = eVariationOn h (Icc a b) := h1'
    have hb1 : BoundedVariationOn h (Icc a a') := hh_bv.mono (Icc_subset_Icc le_rfl (ha'_mem.2.trans hb'_mem.1 |>.trans hb'_mem.2))
    have hb2 : BoundedVariationOn h (Icc b' b) := hh_bv.mono (Icc_subset_Icc (hxstar_mem.1.trans hb'_mem.1) le_rfl)
    rw [← ENNReal.toReal_add hb1 hb2]
    exact ENNReal.toReal_mono hh_bv h_add
  calc ‖∫ x in a..b, F_osc x‖
      ≤ ‖∫ x in a..a', F_osc x‖ + ‖∫ x in a'..b', F_osc x‖ + ‖∫ x in b'..b, F_osc x‖ := by
        rw [h_split]
        exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ 3 * (M + (eVariationOn h (Icc a a')).toReal) / √(c * lam) + 2 * M / √(c * lam) +
          3 * (M + (eVariationOn h (Icc b' b)).toReal) / √(c * lam) := by linarith
    _ = (8 * M + 3 * ((eVariationOn h (Icc a a')).toReal + (eVariationOn h (Icc b' b)).toReal)) / √(c * lam) := by
        ring
    _ ≤ (8 * M + 3 * (eVariationOn h (Icc a b)).toReal) / √(c * lam) := by gcongr
    _ ≤ 8 * (M + (eVariationOn h (Icc a b)).toReal) / √(c * lam) := by
        have : 0 ≤ (eVariationOn h (Icc a b)).toReal := ENNReal.toReal_nonneg
        gcongr; linarith

/-- Second-derivative van der Corput estimate (standard `w = id` form). -/
theorem van_der_corput_second {a b c lam M : ℝ} (hab : a ≤ b) (hc : 0 < c) (hlam : 0 < lam)
    {φ φ' φ'' : ℝ → ℝ} (hφ : ∀ y ∈ Icc a b, HasDerivAt φ (φ' y) y)
    (hφ' : ∀ y ∈ Icc a b, HasDerivAt φ' (φ'' y) y)
    (hφ'_mono : MonotoneOn φ' (Icc a b) ∨ AntitoneOn φ' (Icc a b))
    (hφ''_lb : ∀ y ∈ Icc a b, lam ≤ |φ'' y|)
    {h : ℝ → ℂ} (hh_cont : ContinuousOn h (Icc a b)) (hh_bv : BoundedVariationOn h (Icc a b))
    (hh_bound : ∀ x ∈ Icc a b, ‖h x‖ ≤ M) :
    ‖∫ x in a..b, h x * Complex.exp (Complex.I * (c : ℂ) * (φ x : ℂ))‖ ≤
      8 * (M + (eVariationOn h (Icc a b)).toReal) / √(c * lam) := by
  have h1 := van_der_corput_second_comp hab hc hlam (w := id) (w' := fun _ => 1)
    (fun x _ => hasDerivAt_id x) continuousOn_const (fun _ _ => zero_le_one)
    hφ hφ' hφ'_mono hφ''_lb hh_cont hh_bv hh_bound
  simpa only [id, Complex.ofReal_one, mul_one] using h1

end VanDerCorput

/-! ### Axiom Verification -/

/-- info: 'FormalResearch.Analysis.van_der_corput_first' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Analysis.van_der_corput_first

/-- info: 'FormalResearch.Analysis.van_der_corput_second' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Analysis.van_der_corput_second

end FormalResearch.Analysis
