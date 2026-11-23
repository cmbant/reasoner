module

public import FormalResearch.ModularBootstrap.Upper.Ramped.RampedDesignPhase

/-!
# The three-range summation of the shift cost (`rem:thmU` Step (3), "Shifts"; Lemma `E`-type)

Source: `CFT/notes/n2_ramped_comb.tex`, Lemma `U*` (`rem:thmU`), Step (3), bullet "Shifts": with
`σ = τ(x)/λ ∈ [Φ_n, Φ_{n+1})` and `|x - χ_k| ≥ c λ |σ - Φ_k|`, splitting into `k < n/2`, `|k - n| ≤ n/2` (where
`|k - n| ≥ 3`) and `k > 2n`, as in the proof of `ut:E`.

Pure real analysis, no comb data: for `eGap n k = |Φ_k - [Φ_n, Φ_{n+1}]|` (`Φ_k = (k - 1/4)^{2/3}`),
`shift_core_sum`: `∑_{2 ≤ k ≤ N, k ∉ {n-3, …, n+4}} k^{-4/3}/eGap n k ≤ 18 n^{-2/3} + 6 n^{-1} log n` for `n ≥ 8`
(and every `N`); `ratio_le_three`: each ratio is at most `3 n^{-2/3}`; `lam_phi_sub_le`: the mean-value comparison
`λ(Φ_b - Φ_a) ≤ L(χ_b - χ_a)` from `|τ'| ≤ L` on `[ξ_*/2, ξ_* + 1]`.

All results are proved unconditionally.
-/

@[expose] public section

open Real Filter Topology Set
open scoped Real BigOperators

namespace FormalResearch.ModularBootstrap.Upper.Ramped

open FormalResearch.ModularBootstrap Upper.Comb Upper.Design FormalResearch.ModularBootstrap.Upper.Window
  Upper.Holes

/-- Mean-value lower bound `(2/3) x^{-1/3} (x - y) ≤ x^{2/3} - y^{2/3}` for `0 < y ≤ x`. -/
lemma rpow23_sub_ge {y x : ℝ} (hy : 0 < y) (hyx : y ≤ x) :
    2 / 3 * x ^ (-(1 / 3 : ℝ)) * (x - y) ≤ x ^ (2 / 3 : ℝ) - y ^ (2 / 3 : ℝ) := by
  rcases hyx.eq_or_lt with h | hlt
  · rw [h]; simp
  have hcont : ContinuousOn (fun t : ℝ => t ^ (2 / 3 : ℝ)) (Icc y x) :=
    continuousOn_id.rpow_const fun t _ => Or.inr (by norm_num)
  have hdiff : ∀ t ∈ Ioo y x, HasDerivAt (fun s : ℝ => s ^ (2 / 3 : ℝ))
      (2 / 3 * t ^ (-(1 / 3 : ℝ))) t := fun t ht => by
    have ht0 : 0 < t := lt_trans hy ht.1
    simpa [show (2 / 3 : ℝ) - 1 = -(1 / 3 : ℝ) by norm_num] using
      (hasDerivAt_id t).rpow_const (p := (2 / 3 : ℝ)) (Or.inl ht0.ne')
  obtain ⟨c, hc, hmv⟩ := exists_hasDerivAt_eq_slope (fun t : ℝ => t ^ (2 / 3 : ℝ))
    (fun t => 2 / 3 * t ^ (-(1 / 3 : ℝ))) hlt hcont hdiff
  have hc0 : 0 < c := lt_trans hy hc.1
  rw [eq_div_iff (sub_ne_zero.mpr hlt.ne')] at hmv
  have h1 : x ^ (-(1 / 3 : ℝ)) ≤ c ^ (-(1 / 3 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hc0 hc.2.le (by norm_num)
  have hxy : 0 < x - y := sub_pos.2 hlt
  nlinarith

/-- The distance `|Φ_k - [Φ_n, Φ_{n+1}]|` of the exponent `Φ_k = (k-1/4)^{2/3}` to the cell `n`. -/
noncomputable def eGap (n k : ℕ) : ℝ :=
  if k < n then phiWKB n - phiWKB k else phiWKB k - phiWKB (n + 1)

lemma eGap_lt {n k : ℕ} (hk : 1 ≤ k) (hkn : k < n) :
    2 / 3 * (n : ℝ) ^ (-(1 / 3 : ℝ)) * ((n : ℝ) - k) ≤ eGap n k := by
  unfold eGap
  simp only [hkn, ↓reduceIte]
  unfold phiWKB
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkn' : (k : ℝ) < n := by exact_mod_cast hkn
  have h := rpow23_sub_ge (y := (k : ℝ) - 1 / 4) (x := (n : ℝ) - 1 / 4) (by linarith) (by linarith)
  have hx0 : 0 < (n : ℝ) - 1 / 4 := by linarith
  have h2 : (n : ℝ) ^ (-(1 / 3 : ℝ)) ≤ ((n : ℝ) - 1 / 4) ^ (-(1 / 3 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hx0 (by linarith) (by norm_num)
  have h3 : 0 ≤ (n : ℝ) - k := by linarith
  have : 2 / 3 * (n : ℝ) ^ (-(1 / 3 : ℝ)) * ((n : ℝ) - k) ≤
      2 / 3 * ((n : ℝ) - 1 / 4) ^ (-(1 / 3 : ℝ)) * ((n : ℝ) - 1 / 4 - ((k : ℝ) - 1 / 4)) := by
    rw [show (n : ℝ) - 1 / 4 - ((k : ℝ) - 1 / 4) = (n : ℝ) - k by ring]
    gcongr
  linarith

lemma eGap_gt {n k : ℕ} (hk : n + 1 < k) :
    2 / 3 * (k : ℝ) ^ (-(1 / 3 : ℝ)) * ((k : ℝ) - n - 1) ≤ eGap n k := by
  unfold eGap
  simp only [show ¬ k < n by omega, ↓reduceIte]
  unfold phiWKB
  have hk1 : (n : ℝ) + 1 < k := by exact_mod_cast hk
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h := rpow23_sub_ge (y := ((n + 1 : ℕ) : ℝ) - 1 / 4) (x := (k : ℝ) - 1 / 4)
    (by push_cast; linarith) (by push_cast; linarith)
  have hx0 : 0 < (k : ℝ) - 1 / 4 := by linarith
  have h2 : (k : ℝ) ^ (-(1 / 3 : ℝ)) ≤ ((k : ℝ) - 1 / 4) ^ (-(1 / 3 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hx0 (by linarith) (by norm_num)
  have h3 : 0 ≤ (k : ℝ) - n - 1 := by linarith
  have : 2 / 3 * (k : ℝ) ^ (-(1 / 3 : ℝ)) * ((k : ℝ) - n - 1) ≤
      2 / 3 * ((k : ℝ) - 1 / 4) ^ (-(1 / 3 : ℝ)) * ((k : ℝ) - 1 / 4 - (((n + 1 : ℕ) : ℝ) - 1 / 4)) := by
    rw [show (k : ℝ) - 1 / 4 - (((n + 1 : ℕ) : ℝ) - 1 / 4) = (k : ℝ) - n - 1 by push_cast; ring]
    gcongr
  linarith

lemma rpow_neg43 {t : ℝ} (ht : 0 < t) : t ^ (-(4 / 3 : ℝ)) = t ^ (-(1 / 3 : ℝ)) * t⁻¹ := by
  rw [← Real.rpow_neg_one, ← Real.rpow_add ht]; norm_num

lemma rpow_neg23_le {t : ℝ} (ht : 1 ≤ t) : t ^ (-(2 / 3 : ℝ)) ≤ 1 := 
  Real.rpow_le_one_of_one_le_of_nonpos ht (by norm_num)


/-- Case `2k ≤ n`: `k^{-4/3}/e ≤ 3 k^{-4/3} n^{-2/3}`. -/
lemma ratio_A {n k : ℕ} (hk : 1 ≤ k) (hkn : 2 * k ≤ n) :
    (k : ℝ) ^ (-(4 / 3 : ℝ)) / eGap n k ≤ 3 * ((k : ℝ) ^ (-(4 / 3 : ℝ)) * (n : ℝ) ^ (-(2 / 3 : ℝ))) := by
  have hkn' : k < n := by omega
  have he := eGap_lt hk hkn'
  have hn : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have h2k : (2 : ℝ) * k ≤ n := by exact_mod_cast hkn
  have hp : 0 < (n : ℝ) ^ (-(1 / 3 : ℝ)) := Real.rpow_pos_of_pos hn _
  have e1 : (n : ℝ) ^ (-(1 / 3 : ℝ)) * n = (n : ℝ) ^ (2 / 3 : ℝ) := by
    calc (n : ℝ) ^ (-(1 / 3 : ℝ)) * n = (n : ℝ) ^ (-(1 / 3 : ℝ)) * (n : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hn]; norm_num
  have e2 : (n : ℝ) ^ (-(2 / 3 : ℝ)) = ((n : ℝ) ^ (2 / 3 : ℝ))⁻¹ := Real.rpow_neg hn.le _
  have he0 : 1 / 3 * ((n : ℝ) ^ (-(1 / 3 : ℝ)) * n) ≤ eGap n k := by
    refine le_trans ?_ he
    nlinarith [mul_pos hp hn]
  have hepos : 0 < 1 / 3 * ((n : ℝ) ^ (-(1 / 3 : ℝ)) * n) := by positivity
  have hA : 0 ≤ (k : ℝ) ^ (-(4 / 3 : ℝ)) := by positivity
  calc (k : ℝ) ^ (-(4 / 3 : ℝ)) / eGap n k
      ≤ (k : ℝ) ^ (-(4 / 3 : ℝ)) / (1 / 3 * ((n : ℝ) ^ (-(1 / 3 : ℝ)) * n)) :=
        div_le_div_of_nonneg_left hA hepos he0
    _ = 3 * ((k : ℝ) ^ (-(4 / 3 : ℝ)) * (n : ℝ) ^ (-(2 / 3 : ℝ))) := by
        rw [e1, e2]; field_simp

/-- Case `2k > n`, `k + 4 ≤ n`: `k^{-4/3}/e ≤ (9/2) n^{-1}/(n-k)`. -/
lemma ratio_B {n k : ℕ} (hkn : n < 2 * k) (hk4 : k + 4 ≤ n) :
    (k : ℝ) ^ (-(4 / 3 : ℝ)) / eGap n k ≤ 9 / 2 * ((n : ℝ)⁻¹ / ((n : ℝ) - k)) := by
  have hk1 : 1 ≤ k := by omega
  have hkn' : k < n := by omega
  have he := eGap_lt hk1 hkn'
  have hn : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk1
  have hnk : (4 : ℝ) ≤ (n : ℝ) - k := by
    have : (k : ℝ) + 4 ≤ n := by exact_mod_cast hk4
    linarith
  have hp : 0 < (n : ℝ) ^ (-(1 / 3 : ℝ)) := Real.rpow_pos_of_pos hn _
  have hepos : 0 < 2 / 3 * (n : ℝ) ^ (-(1 / 3 : ℝ)) * ((n : ℝ) - k) := by nlinarith
  have hA : 0 ≤ (k : ℝ) ^ (-(4 / 3 : ℝ)) := by positivity
  -- k^{-4/3} ≤ 3 n^{-4/3}
  have hk43 : (k : ℝ) ^ (-(4 / 3 : ℝ)) ≤ 3 * (n : ℝ) ^ (-(4 / 3 : ℝ)) := by
    have h2 : (n : ℝ) / 2 ≤ k := by
      have : (n : ℝ) < 2 * k := by exact_mod_cast hkn
      linarith
    have h3 : (k : ℝ) ^ (-(4 / 3 : ℝ)) ≤ ((n : ℝ) / 2) ^ (-(4 / 3 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) h2 (by norm_num)
    have h4 : ((n : ℝ) / 2) ^ (-(4 / 3 : ℝ)) = 2 ^ (4 / 3 : ℝ) * (n : ℝ) ^ (-(4 / 3 : ℝ)) := by
      rw [Real.div_rpow hn.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul, mul_comm]
    have h5 : (2 : ℝ) ^ (4 / 3 : ℝ) ≤ 3 := by
      have := rpow23_le (x := 4) (y := 3)
      by_contra hcon
      push Not at hcon
      have h6 : (3 : ℝ) ^ 3 < ((2 : ℝ) ^ (4 / 3 : ℝ)) ^ 3 := pow_lt_pow_left₀ hcon (by norm_num) (by norm_num)
      have h7 : ((2 : ℝ) ^ (4 / 3 : ℝ)) ^ 3 = 2 ^ 4 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
      norm_num [h7] at h6
    have hnn : 0 ≤ (n : ℝ) ^ (-(4 / 3 : ℝ)) := by positivity
    nlinarith
  have h43n := rpow_neg43 hn
  calc (k : ℝ) ^ (-(4 / 3 : ℝ)) / eGap n k
      ≤ (k : ℝ) ^ (-(4 / 3 : ℝ)) / (2 / 3 * (n : ℝ) ^ (-(1 / 3 : ℝ)) * ((n : ℝ) - k)) :=
        div_le_div_of_nonneg_left hA hepos he
    _ ≤ (3 * (n : ℝ) ^ (-(4 / 3 : ℝ))) / (2 / 3 * (n : ℝ) ^ (-(1 / 3 : ℝ)) * ((n : ℝ) - k)) :=
        div_le_div_of_nonneg_right hk43 hepos.le
    _ = 9 / 2 * ((n : ℝ)⁻¹ / ((n : ℝ) - k)) := by
        have h0 : (n : ℝ) - k ≠ 0 := by linarith
        rw [h43n]; field_simp [hp.ne', hn.ne', h0]
        norm_num

/-- Case `k ≥ n + 5`: `k^{-4/3}/e ≤ (3/2) k^{-1}/(k - n - 1)`. -/
lemma ratio_C {n k : ℕ} (hk : n + 5 ≤ k) :
    (k : ℝ) ^ (-(4 / 3 : ℝ)) / eGap n k ≤ 3 / 2 * ((k : ℝ)⁻¹ / ((k : ℝ) - n - 1)) := by
  have he := eGap_gt (n := n) (k := k) (by omega)
  have hkr : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hkn : (n : ℝ) + 5 ≤ k := by exact_mod_cast hk
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hp : 0 < (k : ℝ) ^ (-(1 / 3 : ℝ)) := Real.rpow_pos_of_pos hkr _
  have hd : (4 : ℝ) ≤ (k : ℝ) - n - 1 := by linarith
  have hepos : 0 < 2 / 3 * (k : ℝ) ^ (-(1 / 3 : ℝ)) * ((k : ℝ) - n - 1) := by nlinarith
  have hA : 0 ≤ (k : ℝ) ^ (-(4 / 3 : ℝ)) := by positivity
  have h43 := rpow_neg43 hkr
  calc (k : ℝ) ^ (-(4 / 3 : ℝ)) / eGap n k
      ≤ (k : ℝ) ^ (-(4 / 3 : ℝ)) / (2 / 3 * (k : ℝ) ^ (-(1 / 3 : ℝ)) * ((k : ℝ) - n - 1)) :=
        div_le_div_of_nonneg_left hA hepos he
    _ = 3 / 2 * ((k : ℝ)⁻¹ / ((k : ℝ) - n - 1)) := by
        have h0 : (k : ℝ) - n - 1 ≠ 0 := by linarith
        rw [h43]; field_simp [hp.ne', hkr.ne', h0]


lemma sum_Icc_inv_le (n : ℕ) : ∑ j ∈ Finset.Icc 1 n, (j : ℝ)⁻¹ ≤ 1 + Real.log n := by
  have h := harmonic_le_one_add_log n
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  exact h

/-- Reindexed harmonic bound. -/
lemma sum_inv_reindex_le (n : ℕ) (F : Finset ℕ) (g : ℕ → ℕ) (hinj : Set.InjOn g F)
    (hmaps : ∀ k ∈ F, 1 ≤ g k ∧ g k ≤ n) : ∑ k ∈ F, ((g k : ℕ) : ℝ)⁻¹ ≤ 1 + Real.log n := by
  rw [← Finset.sum_image (f := fun j : ℕ => (j : ℝ)⁻¹) hinj]
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun j _ _ => by positivity))
    (sum_Icc_inv_le n)
  intro j hj
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
  exact Finset.mem_Icc.mpr (hmaps k hk)

/-- The summation index set of the shift cost: `2 ≤ k ≤ N` outside the hole `{n-3, …, n+4}`. -/
abbrev shiftIdx (n N : ℕ) : Finset ℕ := (Finset.Icc 2 N).filter (fun k => k ∉ Finset.Icc (n - 4 + 1) (n + 4))

lemma mem_shiftIdx {n N k : ℕ} (hn : 8 ≤ n) :
    k ∈ shiftIdx n N ↔ 2 ≤ k ∧ k ≤ N ∧ (k + 4 ≤ n ∨ n + 5 ≤ k) := by
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨h1, h2, ?_⟩
    by_contra hcon
    push Not at hcon
    exact h3 ⟨by omega, by omega⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨h1, h2⟩, fun h => ?_⟩
    omega

/-- **Core of the shift estimate** (Lemma `E`-type three-range summation):
`∑_{k ∉ H, 2 ≤ k ≤ N} k^{-4/3}/e_k ≤ 18 n^{-2/3} + 6 log n / n` for `n ≥ 8`. -/
theorem shift_core_sum {n : ℕ} (hn : 8 ≤ n) (N : ℕ) :
    ∑ k ∈ shiftIdx n N, (k : ℝ) ^ (-(4 / 3 : ℝ)) / eGap n k ≤
      18 * (n : ℝ) ^ (-(2 / 3 : ℝ)) + 6 * (Real.log n / n) := by
  have hnr : (8 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  set F := shiftIdx n N with hF
  have hmem : ∀ k, k ∈ F ↔ 2 ≤ k ∧ k ≤ N ∧ (k + 4 ≤ n ∨ n + 5 ≤ k) := fun k => mem_shiftIdx hn
  set r : ℕ → ℝ := fun k => (k : ℝ) ^ (-(4 / 3 : ℝ)) / eGap n k with hr
  rw [← Finset.sum_filter_add_sum_filter_not F (fun k => 2 * k ≤ n),
    ← Finset.sum_filter_add_sum_filter_not (F.filter fun k => ¬ 2 * k ≤ n) (fun k => k < n),
    ← Finset.sum_filter_add_sum_filter_not ((F.filter fun k => ¬ 2 * k ≤ n).filter fun k => ¬ k < n)
      (fun k => k ≤ 2 * n)]
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  have hn1 : (n : ℝ) ^ (-(2 / 3 : ℝ)) * 1 ≥ (n : ℝ)⁻¹ := by
    rw [mul_one, show (-(2 / 3 : ℝ)) = -(2 / 3 : ℝ) from rfl]
    have : (n : ℝ)⁻¹ = (n : ℝ) ^ (-1 : ℝ) := (Real.rpow_neg_one _).symm
    rw [this]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  -- piece A
  have hA : ∑ k ∈ F.filter (fun k => 2 * k ≤ n), r k ≤ 9 * (n : ℝ) ^ (-(2 / 3 : ℝ)) := by
    have h1 : ∑ k ∈ F.filter (fun k => 2 * k ≤ n), r k ≤
        ∑ k ∈ F.filter (fun k => 2 * k ≤ n), 3 * ((k : ℝ) ^ (-(4 / 3 : ℝ)) * (n : ℝ) ^ (-(2 / 3 : ℝ))) := by
      refine Finset.sum_le_sum fun k hk => ?_
      have hk' := Finset.mem_filter.mp hk
      have := (hmem k).1 hk'.1
      exact ratio_A (by omega) hk'.2
    refine h1.trans ?_
    rw [← Finset.mul_sum, ← Finset.sum_mul]
    have h2 : ∑ k ∈ F.filter (fun k => 2 * k ≤ n), (k : ℝ) ^ (-(4 / 3 : ℝ)) ≤ 3 := by
      have := sum_Ioc_rpow_neg_gt_one (p := 4 / 3) (by norm_num) (a := 1) le_rfl N
      simp only [Nat.cast_one, Real.one_rpow] at this
      refine le_trans ?_ (this.trans (by norm_num))
      refine Finset.sum_le_sum_of_subset_of_nonneg (fun k hk => ?_) (fun k _ _ => by positivity)
      have hk' := Finset.mem_filter.mp hk
      have := (hmem k).1 hk'.1
      exact Finset.mem_Ioc.mpr ⟨by omega, this.2.1⟩
    have hp : 0 ≤ (n : ℝ) ^ (-(2 / 3 : ℝ)) := by positivity
    nlinarith
  -- piece B
  have hB : ∑ k ∈ (F.filter fun k => ¬ 2 * k ≤ n).filter (fun k => k < n), r k ≤
      9 / 2 * ((n : ℝ)⁻¹ * (1 + Real.log n)) := by
    set S := (F.filter fun k => ¬ 2 * k ≤ n).filter (fun k => k < n)
    have h1 : ∑ k ∈ S, r k ≤ ∑ k ∈ S, 9 / 2 * ((n : ℝ)⁻¹ * (((n - k : ℕ) : ℝ))⁻¹) := by
      refine Finset.sum_le_sum fun k hk => ?_
      have hk' := Finset.mem_filter.mp hk
      have hk'' := Finset.mem_filter.mp hk'.1
      have h3 := (hmem k).1 hk''.1
      have hlt : k < n := hk'.2
      have h4 : k + 4 ≤ n := by omega
      have := ratio_B (n := n) (k := k) (by omega) h4
      rw [Nat.cast_sub hlt.le]
      exact this.trans (le_of_eq (by ring))
    refine h1.trans ?_
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    have h2 : ∑ k ∈ S, (((n - k : ℕ) : ℝ))⁻¹ ≤ 1 + Real.log n := by
      refine sum_inv_reindex_le n S (fun k => n - k) ?_ ?_
      · intro a ha b hb hab
        have ha' := (Finset.mem_filter.mp ha).2
        have hb' := (Finset.mem_filter.mp hb).2
        simp only at hab
        omega
      · intro k hk
        have hk' := Finset.mem_filter.mp hk
        have hk'' := Finset.mem_filter.mp hk'.1
        have h3 := (hmem k).1 hk''.1
        have hlt : k < n := hk'.2
        exact ⟨by omega, by omega⟩
    have hp : 0 ≤ (n : ℝ)⁻¹ := by positivity
    nlinarith
  -- piece C1
  have hC1 : ∑ k ∈ ((F.filter fun k => ¬ 2 * k ≤ n).filter fun k => ¬ k < n).filter (fun k => k ≤ 2 * n), r k ≤
      3 / 2 * ((n : ℝ)⁻¹ * (1 + Real.log n)) := by
    set S := ((F.filter fun k => ¬ 2 * k ≤ n).filter fun k => ¬ k < n).filter (fun k => k ≤ 2 * n)
    have hmemS : ∀ k ∈ S, n + 5 ≤ k ∧ k ≤ 2 * n := by
      intro k hk
      have hk' := Finset.mem_filter.mp hk
      have hk'' := Finset.mem_filter.mp hk'.1
      have hk3 := Finset.mem_filter.mp hk''.1
      have h3 := (hmem k).1 hk3.1
      refine ⟨?_, hk'.2⟩
      have := hk''.2
      omega
    have h1 : ∑ k ∈ S, r k ≤ ∑ k ∈ S, 3 / 2 * ((n : ℝ)⁻¹ * (((k - n - 1 : ℕ) : ℝ))⁻¹) := by
      refine Finset.sum_le_sum fun k hk => ?_
      obtain ⟨h5, h6⟩ := hmemS k hk
      have := ratio_C (n := n) (k := k) h5
      have hcast : (((k - n - 1 : ℕ) : ℝ)) = (k : ℝ) - n - 1 := by
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
      rw [hcast]
      refine this.trans ?_
      have hkn : (n : ℝ) ≤ k := by exact_mod_cast (by omega : n ≤ k)
      have hd : (0 : ℝ) < (k : ℝ) - n - 1 := by
        have : (n : ℝ) + 5 ≤ k := by exact_mod_cast h5
        linarith
      have hkinv : (k : ℝ)⁻¹ ≤ (n : ℝ)⁻¹ := inv_anti₀ hn0 hkn
      have : (k : ℝ)⁻¹ / ((k : ℝ) - n - 1) ≤ (n : ℝ)⁻¹ * ((k : ℝ) - n - 1)⁻¹ := by
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right hkinv (by positivity)
      linarith
    refine h1.trans ?_
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    have h2 : ∑ k ∈ S, (((k - n - 1 : ℕ) : ℝ))⁻¹ ≤ 1 + Real.log n := by
      refine sum_inv_reindex_le n S (fun k => k - n - 1) ?_ ?_
      · intro a ha b hb hab
        obtain ⟨ha5, _⟩ := hmemS a ha
        obtain ⟨hb5, _⟩ := hmemS b hb
        simp only at hab
        omega
      · intro k hk
        obtain ⟨h5, h6⟩ := hmemS k hk
        exact ⟨by omega, by omega⟩
    have hp : 0 ≤ (n : ℝ)⁻¹ := by positivity
    nlinarith
  -- piece C2
  have hC2 : ∑ k ∈ ((F.filter fun k => ¬ 2 * k ≤ n).filter fun k => ¬ k < n).filter (fun k => ¬ k ≤ 2 * n), r k ≤
      3 * (n : ℝ)⁻¹ := by
    set S := ((F.filter fun k => ¬ 2 * k ≤ n).filter fun k => ¬ k < n).filter (fun k => ¬ k ≤ 2 * n)
    have hmemS : ∀ k ∈ S, 2 * n < k := by
      intro k hk
      have hk' := Finset.mem_filter.mp hk
      have := hk'.2
      omega
    have h1 : ∑ k ∈ S, r k ≤ ∑ k ∈ S, 6 * (k : ℝ) ^ (-(2 : ℝ)) := by
      refine Finset.sum_le_sum fun k hk => ?_
      have hk2 := hmemS k hk
      have hk' := Finset.mem_filter.mp hk
      have hk'' := Finset.mem_filter.mp hk'.1
      have hk3 := Finset.mem_filter.mp hk''.1
      have h3 := (hmem k).1 hk3.1
      have h5 : n + 5 ≤ k := by omega
      have := ratio_C (n := n) (k := k) h5
      have hkr : (8 : ℝ) < k := by
        have : (2 * n : ℝ) < k := by exact_mod_cast hk2
        linarith
      have hd : (k : ℝ) / 4 ≤ (k : ℝ) - n - 1 := by
        have : (2 * n : ℝ) < k := by exact_mod_cast hk2
        linarith
      have hd0 : 0 < (k : ℝ) / 4 := by linarith
      refine this.trans ?_
      have e : (k : ℝ) ^ (-(2 : ℝ)) = ((k : ℝ) * k)⁻¹ := by
        rw [Real.rpow_neg (by linarith), Real.rpow_two, sq, ]
      rw [e]
      calc 3 / 2 * ((k : ℝ)⁻¹ / ((k : ℝ) - n - 1)) ≤ 3 / 2 * ((k : ℝ)⁻¹ / ((k : ℝ) / 4)) := by
            gcongr
        _ = 6 * ((k : ℝ) * k)⁻¹ := by field_simp; ring
    refine h1.trans ?_
    rw [← Finset.mul_sum]
    have h2 : ∑ k ∈ S, (k : ℝ) ^ (-(2 : ℝ)) ≤ (n : ℝ)⁻¹ / 2 := by
      have := sum_Ioc_rpow_neg_gt_one (p := 2) (by norm_num) (a := 2 * n) (by omega) N
      refine le_trans ?_ (this.trans (le_of_eq ?_))
      · refine Finset.sum_le_sum_of_subset_of_nonneg (fun k hk => ?_) (fun k _ _ => by positivity)
        have hk2 := hmemS k hk
        have hk' := Finset.mem_filter.mp hk
        have hk'' := Finset.mem_filter.mp hk'.1
        have hk3 := Finset.mem_filter.mp hk''.1
        have h3 := (hmem k).1 hk3.1
        exact Finset.mem_Ioc.mpr ⟨hk2, h3.2.1⟩
      · push_cast
        rw [show (1 - 2 : ℝ) = -1 by norm_num, Real.rpow_neg_one]
        field_simp
        norm_num
    nlinarith
  -- assemble
  have hnn : (n : ℝ)⁻¹ ≤ (n : ℝ) ^ (-(2 / 3 : ℝ)) := by linarith [hn1]
  have hq : Real.log n / n = (n : ℝ)⁻¹ * Real.log n := by rw [div_eq_inv_mul]
  rw [hq]
  nlinarith [hA, hB, hC1, hC2, mul_nonneg (inv_nonneg.2 hn0.le) hlog]


lemma eGap_pos {n k : ℕ} (hk : 2 ≤ k) (h : k + 4 ≤ n ∨ n + 5 ≤ k) : 0 < eGap n k := by
  rcases h with h | h
  · have := eGap_lt (n := n) (k := k) (by omega) (by omega)
    have hn : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hnk : (4 : ℝ) ≤ (n : ℝ) - k := by
      have : (k : ℝ) + 4 ≤ n := by exact_mod_cast h
      linarith
    have hp : 0 < (n : ℝ) ^ (-(1 / 3 : ℝ)) := Real.rpow_pos_of_pos hn _
    have : 0 < 2 / 3 * (n : ℝ) ^ (-(1 / 3 : ℝ)) * ((n : ℝ) - k) := by nlinarith
    linarith [eGap_lt (n := n) (k := k) (by omega) (by omega)]
  · have hkr : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    have hkn : (n : ℝ) + 5 ≤ k := by exact_mod_cast h
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hp : 0 < (k : ℝ) ^ (-(1 / 3 : ℝ)) := Real.rpow_pos_of_pos hkr _
    have : 0 < 2 / 3 * (k : ℝ) ^ (-(1 / 3 : ℝ)) * ((k : ℝ) - n - 1) := by nlinarith
    linarith [eGap_gt (n := n) (k := k) (by omega)]

/-- Uniform bound on the individual ratios: `k^{-4/3}/e_k ≤ 3 n^{-2/3}` outside the hole (`n ≥ 8`). -/
lemma ratio_le_three {n k : ℕ} (hn : 8 ≤ n) (hk : 2 ≤ k) (h : k + 4 ≤ n ∨ n + 5 ≤ k) :
    (k : ℝ) ^ (-(4 / 3 : ℝ)) / eGap n k ≤ 3 * (n : ℝ) ^ (-(2 / 3 : ℝ)) := by
  have hnr : (8 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hinv : (n : ℝ)⁻¹ ≤ (n : ℝ) ^ (-(2 / 3 : ℝ)) := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hp : 0 ≤ (n : ℝ) ^ (-(2 / 3 : ℝ)) := by positivity
  have hkk : (k : ℝ) ^ (-(4 / 3 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast (by omega : 1 ≤ k)) (by norm_num)
  by_cases hA : 2 * k ≤ n
  · refine (ratio_A (by omega) hA).trans ?_
    nlinarith [Real.rpow_nonneg (Nat.cast_nonneg k) (-(4 / 3 : ℝ))]
  · by_cases hlt : k < n
    · have h4 : k + 4 ≤ n := by omega
      refine (ratio_B (by omega) h4).trans ?_
      have hnk : (4 : ℝ) ≤ (n : ℝ) - k := by
        have : (k : ℝ) + 4 ≤ n := by exact_mod_cast h4
        linarith
      have : (n : ℝ)⁻¹ / ((n : ℝ) - k) ≤ (n : ℝ)⁻¹ / 4 :=
        div_le_div_of_nonneg_left (by positivity) (by norm_num) hnk
      nlinarith
    · have h5 : n + 5 ≤ k := by omega
      refine (ratio_C h5).trans ?_
      have hkr : (n : ℝ) + 5 ≤ k := by exact_mod_cast h5
      have hd : (4 : ℝ) ≤ (k : ℝ) - n - 1 := by linarith
      have hkinv : (k : ℝ)⁻¹ ≤ (n : ℝ)⁻¹ := inv_anti₀ hn0 (by linarith)
      have : (k : ℝ)⁻¹ / ((k : ℝ) - n - 1) ≤ (n : ℝ)⁻¹ / 4 :=
        div_le_div₀ (by positivity) hkinv (by norm_num) hd
      nlinarith

lemma lam_phi_sub_le {L : ℝ} (hL : ∀ z ∈ Icc (xiStar / 2) (xiStar + 1), |deriv langerTau z| ≤ L)
    {c' a b : ℝ} (hc' : 0 < c') (ha : 1 / 4 ≤ a) (hab : a ≤ b)
    (hb : chiQuantile c' b ≤ xiStar + 1) :
    lambdaComb c' * (phiQuantile b - phiQuantile a) ≤ L * (chiQuantile c' b - chiQuantile c' a) := by
  have hxs := xiStar_pos
  have h1 := (chiQuantile_spec hc' ha).1
  have hle := chiQuantile_mono_le hc' ha hab
  have h := langerTau_sub_le (a := xiStar / 2) (b := xiStar + 1) (C := L) (by linarith) hL
    (by linarith) hle hb
  rw [langerTau_chiQuantile hc' (ha.trans hab), langerTau_chiQuantile hc' ha] at h
  linarith



/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.shift_core_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms shift_core_sum

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.ratio_le_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ratio_le_three

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.lam_phi_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lam_phi_sub_le

end FormalResearch.ModularBootstrap.Upper.Ramped
