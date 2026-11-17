module

public import FormalResearch.Special.LatticePhase

/-!
# Elementary bounds for `ψ` on vertical lines `Re z ∈ [¼, 1]`

Source: `constants.tex`, proof of `lem:latticesum`: "`Re ψ(z) ≤ log(1+|z|) + C` for `Re z ≥ ¼`" and
"`Re ψ(½ + is) ≥ ψ(½) > -2`".  Both are proved here from Gauss' series (`Barnes.digamma_eq_series`),
without Stirling's formula:

* `re_digamma_half_line_ge` : `Re ψ(½ + iy) ≥ -3` (termwise comparison with `ψ(½) = -γ - 2 log 2`;
  numerically `ψ(½) = -1.9635…`, the paper's `> -2` is not needed);
* `re_digamma_upper` : for `¼ ≤ x ≤ 1`, `Re ψ(x + iy) ≤ log(1 + |y|) + 5` (split Gauss' series at
  `N ≈ |y|`: the first `N` terms are `≤ H_N ≤ 1 + log N`, the tail is `≤ (4/3) y²/N²` by telescoping);
* `digamma_conj` : `ψ(conj z) = conj ψ(z)` for `Re z > 0`.
-/

@[expose] public section

namespace FormalResearch.Special.Lattice

open Filter Topology Set Complex Barnes

local notation "γ" => Real.eulerMascheroniConstant

lemma digamma_conj {z : ℂ} (hz : 0 < z.re) : digamma (starRingEnd ℂ z) = starRingEnd ℂ (digamma z) := by
  have hz' : 0 < (starRingEnd ℂ z).re := by simpa using hz
  rw [digamma_eq_series hz, digamma_eq_series hz', map_add, RCLike.conj_tsum]
  congr 1
  · simp
  · congr 1; ext k; simp

lemma re_psiTerm (x y : ℝ) (k : ℕ) (hk : 0 < (k : ℝ) + x) :
    (psiTerm ((x : ℂ) + y * I) k).re = 1 / ((k : ℝ) + 1) - ((k : ℝ) + x) / (((k : ℝ) + x) ^ 2 + y ^ 2) := by
  unfold psiTerm
  have h1 : (1 : ℂ) / ((k : ℂ) + 1) = ((1 / ((k : ℝ) + 1) : ℝ) : ℂ) := by push_cast; rfl
  have h2 : (k : ℂ) + ((x : ℂ) + y * I) = (((k : ℝ) + x : ℝ) : ℂ) + (y : ℂ) * I := by push_cast; ring
  rw [h1, h2, Complex.sub_re, Complex.ofReal_re, one_div (_ + _ * I), Complex.inv_re]
  simp [Complex.normSq_apply, sq]

lemma re_digamma_eq {z : ℂ} (hz : 0 < z.re) :
    (digamma z).re = -γ + ∑' k : ℕ, (psiTerm z k).re := by
  have e : ∑' k : ℕ, ((1 : ℂ) / ((k : ℂ) + 1) - 1 / ((k : ℂ) + z)) = ∑' k, psiTerm z k := rfl
  rw [digamma_eq_series hz, e, Complex.add_re, Complex.re_tsum (summable_psiTerm hz.le)]
  simp

lemma summable_re_psiTerm {z : ℂ} (hz : 0 < z.re) : Summable (fun k : ℕ => (psiTerm z k).re) :=
  (Complex.hasSum_re (summable_psiTerm hz.le).hasSum).summable

/-- Lower bound on the critical line: `Re ψ(½ + iy) ≥ -3`. -/
theorem re_digamma_half_line_ge (y : ℝ) : -3 ≤ (digamma (1 / 2 + y * I)).re := by
  have hz : 0 < ((1 / 2 : ℂ) + y * I).re := by simp
  have hz0 : 0 < (((1 : ℝ) / 2 : ℝ) : ℂ).re := by simp
  have h0 : (digamma (1 / 2 : ℂ)).re = -2 * Real.log 2 - γ := by
    have hl2 : (Complex.log 2).re = Real.log 2 := by simpa using Complex.log_ofReal_re 2
    rw [digamma_one_half]; simp [hl2]
  have e1 : (digamma ((1 / 2 : ℂ) + y * I)).re = -γ + ∑' k : ℕ, (psiTerm ((1 / 2 : ℂ) + y * I) k).re :=
    re_digamma_eq hz
  have e0 : (digamma (1 / 2 : ℂ)).re = -γ + ∑' k : ℕ, (psiTerm (1 / 2 : ℂ) k).re :=
    re_digamma_eq (by simp)
  have hle : ∑' k : ℕ, (psiTerm (1 / 2 : ℂ) k).re ≤ ∑' k : ℕ, (psiTerm ((1 / 2 : ℂ) + y * I) k).re := by
    refine Summable.tsum_le_tsum (fun k => ?_) (summable_re_psiTerm (by simp)) (summable_re_psiTerm hz)
    have a1 := re_psiTerm (1 / 2) 0 k (by positivity)
    have a2 := re_psiTerm (1 / 2) y k (by positivity)
    push_cast at a1 a2
    simp only [zero_mul, add_zero] at a1
    rw [a1, a2]
    have hk : (0 : ℝ) < (k : ℝ) + 1 / 2 := by positivity
    have : ((k : ℝ) + 1 / 2) / (((k : ℝ) + 1 / 2) ^ 2 + y ^ 2) ≤ ((k : ℝ) + 1 / 2) / (((k : ℝ) + 1 / 2) ^ 2 + 0 ^ 2) := by
      apply div_le_div_of_nonneg_left hk.le (by positivity); nlinarith [sq_nonneg y]
    linarith
  have hg := Real.eulerMascheroniConstant_lt_two_thirds
  have hl := Real.log_two_lt_d9
  rw [h0] at e0
  linarith

lemma hasSum_telescope (f : ℕ → ℝ) (hf : ∀ k, f (k + 1) ≤ f k) (hlim : Tendsto f atTop (𝓝 0)) :
    HasSum (fun k => f k - f (k + 1)) (f 0) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun i => sub_nonneg.mpr (hf i))]
  have : (fun n => ∑ i ∈ Finset.range n, (f i - f (i + 1))) = fun n => f 0 - f n := by
    ext n; exact Finset.sum_range_sub' f n
  rw [this]
  simpa using (tendsto_const_nhds (x := f 0)).sub hlim


lemma re_psiTerm_eq' {x y : ℝ} (hx : 1 / 4 ≤ x) (k : ℕ) :
    (psiTerm ((x : ℂ) + y * I) k).re =
      1 / ((k : ℝ) + 1) - ((k : ℝ) + x) / (((k : ℝ) + x) ^ 2 + y ^ 2) :=
  re_psiTerm x y k (by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)

/-- The telescoping comparison function for the tail. -/
noncomputable def tailF (x : ℝ) (N k : ℕ) : ℝ := 1 / ((k : ℝ) + N + x - 1 / 2)

lemma tailF_pos {x : ℝ} (hx : 1 / 4 ≤ x) {N : ℕ} (hN : 1 ≤ N) (k : ℕ) :
    0 < (k : ℝ) + N + x - 1 / 2 := by
  have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have : (1 : ℝ) ≤ N := by exact_mod_cast hN
  linarith

lemma tailF_mono {x : ℝ} (hx : 1 / 4 ≤ x) {N : ℕ} (hN : 1 ≤ N) (k : ℕ) :
    tailF x N (k + 1) ≤ tailF x N k := by
  unfold tailF
  apply one_div_le_one_div_of_le (tailF_pos hx hN k)
  push_cast; linarith

lemma tailF_tendsto (x : ℝ) (N : ℕ) : Tendsto (tailF x N) atTop (𝓝 0) := by
  unfold tailF
  have h : Tendsto (fun k : ℕ => (k : ℝ) + ((N : ℝ) + x - 1 / 2)) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have h2 : Tendsto (fun k : ℕ => ((k : ℝ) + ((N : ℝ) + x - 1 / 2))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp h
  refine h2.congr (fun k => ?_)
  rw [one_div]; ring_nf

lemma tailF_diff {x : ℝ} (hx : 1 / 4 ≤ x) {N : ℕ} (hN : 1 ≤ N) (k : ℕ) :
    tailF x N k - tailF x N (k + 1) = 1 / (((k : ℝ) + N + x) ^ 2 - 1 / 4) := by
  unfold tailF
  push_cast
  have hpos := tailF_pos hx hN k
  set a : ℝ := (k : ℝ) + N + x with ha
  have h1 : (k : ℝ) + N + x - 1 / 2 = a - 1 / 2 := by linarith
  have h2 : ((k : ℝ) + 1 + N + x - 1 / 2) = a + 1 / 2 := by linarith
  rw [h1, h2, show a ^ 2 - 1 / 4 = (a - 1 / 2) * (a + 1 / 2) by ring]
  have h3 : a - 1 / 2 ≠ 0 := by rw [← h1]; exact hpos.ne'
  have h4 : a + 1 / 2 ≠ 0 := by rw [← h2] at *; linarith
  rw [div_sub_div _ _ h3 h4]
  congr 1; ring

lemma tail_term_le {x : ℝ} (y : ℝ) (hx : 1 / 4 ≤ x) (hx1 : x ≤ 1) {N : ℕ} (hN : 1 ≤ N) (k : ℕ) :
    (psiTerm ((x : ℂ) + y * I) (k + N)).re ≤ y ^ 2 / N * (tailF x N k - tailF x N (k + 1)) := by
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  rw [re_psiTerm_eq' hx (k + N), tailF_diff hx hN k]
  push_cast
  set a : ℝ := (k : ℝ) + N + x with ha
  have hapos : 1 / 4 ≤ a := by linarith
  have hNa : (N : ℝ) ≤ a := by linarith
  have e1 : 1 / ((k : ℝ) + N + 1) ≤ 1 / a := by
    apply one_div_le_one_div_of_le (by linarith); linarith
  have e2 : 1 / a - a / (a ^ 2 + y ^ 2) = y ^ 2 / (a * (a ^ 2 + y ^ 2)) := by
    field_simp; ring
  have e3 : y ^ 2 / (a * (a ^ 2 + y ^ 2)) ≤ y ^ 2 / a ^ 3 := by
    apply div_le_div_of_nonneg_left (sq_nonneg y) (by positivity); nlinarith [sq_nonneg y, sq_nonneg a]
  have e5 : y ^ 2 / a ^ 3 ≤ y ^ 2 / N * (1 / (a ^ 2 - 1 / 4)) := by
    have hq : 0 < a ^ 2 - 1 / 4 := by nlinarith
    have : y ^ 2 / a ^ 3 = y ^ 2 / (a * a ^ 2) := by ring
    rw [this, mul_one_div, div_div]
    apply div_le_div_of_nonneg_left (sq_nonneg y) (by positivity)
    nlinarith
  have : (1 : ℝ) / ((k : ℝ) + N + 1) - ((k : ℝ) + N + x) / (((k : ℝ) + N + x) ^ 2 + y ^ 2) ≤
      1 / a - a / (a ^ 2 + y ^ 2) := by
    rw [ha] at e1 ⊢; linarith
  linarith

lemma tail_sum_le {x : ℝ} (y : ℝ) (hx : 1 / 4 ≤ x) (hx1 : x ≤ 1) {N : ℕ} (hN : 1 ≤ N)
    (hNy : |y| ≤ N) :
    ∑' k : ℕ, (psiTerm ((x : ℂ) + y * I) (k + N)).re ≤ 4 / 3 := by
  have hz : 0 < ((x : ℂ) + y * I).re := by simp; linarith
  have hs2 : Summable (fun k : ℕ => (psiTerm ((x : ℂ) + y * I) (k + N)).re) :=
    (summable_nat_add_iff N).mpr (summable_re_psiTerm hz)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hsum := (hasSum_telescope (tailF x N) (tailF_mono hx hN) (tailF_tendsto x N)).mul_left
    (y ^ 2 / N)
  have h2 : ∑' k : ℕ, (psiTerm ((x : ℂ) + y * I) (k + N)).re ≤ y ^ 2 / N * tailF x N 0 := by
    rw [← hsum.tsum_eq]
    exact Summable.tsum_le_tsum (tail_term_le y hx hx1 hN) hs2 hsum.summable
  have hf0 : tailF x N 0 ≤ 4 / 3 / N := by
    unfold tailF; push_cast; simp only [zero_add]
    rw [div_le_div_iff₀ (by linarith) hNpos]
    nlinarith
  calc _ ≤ y ^ 2 / N * tailF x N 0 := h2
    _ ≤ y ^ 2 / N * (4 / 3 / N) := mul_le_mul_of_nonneg_left hf0 (by positivity)
    _ = 4 / 3 * (y ^ 2 / N ^ 2) := by field_simp
    _ ≤ 4 / 3 * 1 := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        rw [div_le_one (by positivity)]
        nlinarith [sq_abs y, abs_nonneg y]
    _ = 4 / 3 := by ring

lemma head_sum_le {x : ℝ} (y : ℝ) (hx : 1 / 4 ≤ x) (N : ℕ) :
    ∑ i ∈ Finset.range N, (psiTerm ((x : ℂ) + y * I) i).re ≤ 1 + Real.log N := by
  have hh : ∑ i ∈ Finset.range N, (psiTerm ((x : ℂ) + y * I) i).re ≤
      ∑ i ∈ Finset.range N, (1 / ((i : ℝ) + 1)) := by
    refine Finset.sum_le_sum (fun i _ => ?_)
    rw [re_psiTerm_eq' hx i]
    have : 0 ≤ ((i : ℝ) + x) / (((i : ℝ) + x) ^ 2 + y ^ 2) := by
      have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
      apply div_nonneg (by linarith) (by positivity)
    linarith
  have h2 := harmonic_le_one_add_log N
  have h3 : ((harmonic N : ℚ) : ℝ) = ∑ i ∈ Finset.range N, (1 / ((i : ℝ) + 1)) := by
    simp [harmonic]
  linarith

/-- Upper bound: `Re ψ(x + iy) ≤ log(1+|y|) + 5` for `¼ ≤ x ≤ 1`. -/
theorem re_digamma_upper {x y : ℝ} (hx : 1 / 4 ≤ x) (hx1 : x ≤ 1) :
    (digamma ((x : ℂ) + y * I)).re ≤ Real.log (1 + |y|) + 5 := by
  have hz : 0 < ((x : ℂ) + y * I).re := by simp; linarith
  rw [re_digamma_eq hz]
  have hs := summable_re_psiTerm hz
  set N : ℕ := ⌈|y|⌉₊ + 1 with hNdef
  have hN1 : (1 : ℝ) ≤ N := by simp [hNdef]
  have hNy : |y| ≤ N := by
    have := Nat.le_ceil |y|
    simp only [hNdef]; push_cast; linarith
  have hNy2 : (N : ℝ) ≤ 2 * (1 + |y|) := by
    have := Nat.ceil_lt_add_one (abs_nonneg y)
    simp only [hNdef]; push_cast; linarith [abs_nonneg y]
  have hNpos : (0 : ℝ) < N := by linarith
  rw [← hs.sum_add_tsum_nat_add N]
  have h1 := head_sum_le y hx N
  have h2 := tail_sum_le y hx hx1 (N := N) (by exact_mod_cast hN1) hNy
  have hlog : Real.log N ≤ Real.log 2 + Real.log (1 + |y|) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    exact Real.log_le_log hNpos hNy2
  have hl := Real.log_two_lt_d9
  have hg := Real.one_half_lt_eulerMascheroniConstant
  linarith

end FormalResearch.Special.Lattice
