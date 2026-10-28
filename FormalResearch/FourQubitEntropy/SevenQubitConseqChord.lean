import Mathlib

/-!
# The two-spike majorisation bound (Karamata, chord form)

If `h` is convex on `[0, M]`, `0 < c < M`, and `e_i ∈ [0, M]` (`i ∈ s`) sum to `c + M`, then
`∑ h(e_i) ≤ (|s| - 2) h(0) + h(M) + h(c)`: the vector `(M, c, 0, …, 0)` majorises every such vector.

Proof.  `h ≤ L` on `[0,M]` for the piecewise-linear interpolant
`L(e) = h(0) + s₁ e + (s₂ - s₁)(e - c)₊` (`s₁ ≤ s₂` by convexity), and `∑ (e_i - c)₊ ≤ M - c`
because at most one entry exceeds `M`... more precisely, either at most one `e_i > c` (each
`(e_i - c)₊ ≤ M - c`) or at least two, whence `∑ (e_i-c)₊ ≤ (c+M) - 2c`.
-/

open Finset

namespace FormalResearch.FourQubitEntropy.SevenQubitConseq

theorem sum_pos_part_le {α : Type*} (s : Finset α) (e : α → ℝ) {M c : ℝ} (hc0 : 0 < c) (hcM : c < M)
    (he0 : ∀ i ∈ s, 0 ≤ e i) (heM : ∀ i ∈ s, e i ≤ M) (hsum : ∑ i ∈ s, e i = c + M) :
    ∑ i ∈ s, max (e i - c) 0 ≤ M - c := by
  classical
  set B := s.filter (fun i => c < e i) with hB
  have hsplit : ∑ i ∈ s, max (e i - c) 0 = ∑ i ∈ B, (e i - c) := by
    rw [hB, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : c < e i
    · rw [if_pos h, max_eq_left (by linarith)]
    · rw [if_neg h, max_eq_right (by linarith [not_lt.1 h])]
  rw [hsplit]
  by_cases hcard : B.card ≤ 1
  · calc ∑ i ∈ B, (e i - c) ≤ B.card • (M - c) := by
          apply Finset.sum_le_card_nsmul
          intro i hi
          have := (Finset.mem_filter.1 hi).1
          linarith [heM i this]
      _ ≤ 1 • (M - c) := by
          rw [nsmul_eq_mul, nsmul_eq_mul]
          have : (B.card : ℝ) ≤ 1 := by exact_mod_cast hcard
          push_cast
          nlinarith
      _ = M - c := by simp
  · have h2 : (2 : ℝ) ≤ B.card := by
      have : 2 ≤ B.card := by omega
      exact_mod_cast this
    have hsub : ∑ i ∈ B, e i ≤ ∑ i ∈ s, e i :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun i hi _ => he0 i hi)
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    nlinarith

theorem chord_reduction {α : Type*} (s : Finset α) (e : α → ℝ) (h : ℝ → ℝ) {M c : ℝ}
    (hc0 : 0 < c) (hcM : c < M) (hconv : ConvexOn ℝ (Set.Icc 0 M) h)
    (he0 : ∀ i ∈ s, 0 ≤ e i) (heM : ∀ i ∈ s, e i ≤ M) (hsum : ∑ i ∈ s, e i = c + M) :
    ∑ i ∈ s, h (e i) ≤ s.card * h 0 + (h M - h 0) + (h c - h 0) := by
  have hM0 : 0 < M := hc0.trans hcM
  have hMc : 0 < M - c := sub_pos.2 hcM
  set s1 := (h c - h 0) / c with hs1
  set s2 := (h M - h c) / (M - c) with hs2
  have h0m : (0 : ℝ) ∈ Set.Icc 0 M := ⟨le_rfl, hM0.le⟩
  have hcm : c ∈ Set.Icc 0 M := ⟨hc0.le, hcM.le⟩
  have hMm : M ∈ Set.Icc 0 M := ⟨hM0.le, le_rfl⟩
  -- slopes
  have hslope : s1 ≤ s2 := by
    have := hconv.2 h0m hMm (show (0 : ℝ) ≤ 1 - c / M by rw [sub_nonneg, div_le_one hM0]; exact hcM.le)
      (show (0 : ℝ) ≤ c / M by positivity) (show (1 - c / M) + c / M = 1 by ring)
    simp only [smul_eq_mul, mul_zero, zero_add] at this
    have e1 : c / M * M = c := by field_simp
    rw [e1] at this
    rw [hs1, hs2, div_le_div_iff₀ hc0 hMc]
    have e2 : (1 - c / M) * h 0 + c / M * h M = h 0 + c / M * (h M - h 0) := by ring
    rw [e2] at this
    have : (h c - h 0) * M ≤ c * (h M - h 0) := by
      have h3 : h c - h 0 ≤ c / M * (h M - h 0) := by linarith
      calc (h c - h 0) * M ≤ c / M * (h M - h 0) * M := mul_le_mul_of_nonneg_right h3 hM0.le
        _ = c * (h M - h 0) := by field_simp
    nlinarith
  -- h ≤ L
  have hL : ∀ x ∈ Set.Icc (0 : ℝ) M, h x ≤ h 0 + s1 * x + (s2 - s1) * max (x - c) 0 := by
    intro x hx
    rcases le_total x c with hxc | hxc
    · have := hconv.2 h0m hcm
        (show (0 : ℝ) ≤ 1 - x / c by rw [sub_nonneg, div_le_one hc0]; exact hxc)
        (show (0 : ℝ) ≤ x / c from div_nonneg hx.1 hc0.le) (show (1 - x / c) + x / c = 1 by ring)
      simp only [smul_eq_mul, mul_zero, zero_add] at this
      have e1 : x / c * c = x := by field_simp
      rw [e1] at this
      rw [max_eq_right (by linarith)]
      have e2 : (1 - x / c) * h 0 + x / c * h c = h 0 + s1 * x := by
        rw [hs1]; field_simp; ring
      linarith
    · have := hconv.2 hcm hMm
        (show (0 : ℝ) ≤ 1 - (x - c) / (M - c) by rw [sub_nonneg, div_le_one hMc]; linarith [hx.2])
        (show (0 : ℝ) ≤ (x - c) / (M - c) from div_nonneg (by linarith) hMc.le)
        (show (1 - (x - c) / (M - c)) + (x - c) / (M - c) = 1 by ring)
      simp only [smul_eq_mul] at this
      have e1 : (1 - (x - c) / (M - c)) * c + (x - c) / (M - c) * M = x := by
        field_simp; ring
      rw [e1] at this
      rw [max_eq_left (by linarith)]
      have e2 : (1 - (x - c) / (M - c)) * h c + (x - c) / (M - c) * h M =
          h 0 + s1 * x + (s2 - s1) * (x - c) := by
        rw [hs1, hs2]; field_simp; ring
      linarith
  have hpos := sum_pos_part_le s e hc0 hcM he0 heM hsum
  calc ∑ i ∈ s, h (e i) ≤ ∑ i ∈ s, (h 0 + s1 * e i + (s2 - s1) * max (e i - c) 0) :=
        Finset.sum_le_sum fun i hi => hL _ ⟨he0 i hi, heM i hi⟩
    _ = s.card * h 0 + s1 * (c + M) + (s2 - s1) * ∑ i ∈ s, max (e i - c) 0 := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hsum]
        simp
    _ ≤ s.card * h 0 + s1 * (c + M) + (s2 - s1) * (M - c) := by
        have : 0 ≤ s2 - s1 := sub_nonneg.2 hslope
        nlinarith
    _ = s.card * h 0 + (h M - h 0) + (h c - h 0) := by
        rw [hs1, hs2]; field_simp; ring

end FormalResearch.FourQubitEntropy.SevenQubitConseq
