module

public import Mathlib

/-!
# A uniform bound for Cauchy-kernel sums over a separated sequence

Generic real analysis, no Airy content.  **Proved.**  Let `c : ℕ → ℝ` be positive with

* growth `κ (n+1)² ≤ c_n⁶`,
* separation `s |n - m| ≤ |c_n - c_m| · max(c_n, c_m)²` for `n ≠ m` (the zeros `√(-a_n)` of `Ai` have `c_n³ ≍ n`, so
  `|c_n - c_m| ≳ |n - m| / max(c_n,c_m)²`),

and put `r_n = 1/(4 c_n²)`.  Then (`separated_kernel_sum`) there is `K` (depending on `s, κ` only) with
`Σ_{n<N} r_n² / ((t - c_n)² + r_n²) ≤ K` for every real `t` and every `N`.

Proof: let `m < N` minimise `|t - c_n|`; for `n ≠ m` one has `|c_n - c_m| ≤ 2|t - c_n|`; if `c_m ≤ 2 c_n` the separation gives
`r_n²/(t-c_n)² ≤ 4/(s²(n-m)²)`, and if `c_m > 2 c_n` then `|t - c_n| ≥ c_n/2` and the term is `≤ 1/(4 c_n⁶) ≤ 1/(4κ(n+1)²)`;
both are summable (the first over `ℤ`).  The `m`-th term is `≤ 1`.
-/

@[expose] public section

open Finset

namespace FormalResearch.Hardy

/-- The two pointwise bounds for a single kernel term. -/
lemma kernel_term_le {c d : ℝ} (hc : 0 < c) (hd : 0 < d) :
    (1 / (4 * c ^ 2)) ^ 2 / (d ^ 2 + (1 / (4 * c ^ 2)) ^ 2) ≤ 1 / (16 * c ^ 4 * d ^ 2) := by
  have hr : (1 / (4 * c ^ 2)) ^ 2 = 1 / (16 * c ^ 4) := by
    field_simp; ring
  rw [hr]
  have h1 : 1 / (16 * c ^ 4) / (d ^ 2 + 1 / (16 * c ^ 4)) ≤ 1 / (16 * c ^ 4) / d ^ 2 := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    linarith [show 0 < 1 / (16 * c ^ 4) by positivity]
  refine h1.trans (le_of_eq ?_)
  field_simp

lemma kernel_term_le_one {r d : ℝ} (hr : 0 < r) : r ^ 2 / (d ^ 2 + r ^ 2) ≤ 1 := by
  rw [div_le_one (by positivity)]
  nlinarith [sq_nonneg d]

/-- **Uniform bound for the kernel sum over a separated sequence.** -/
theorem separated_kernel_sum {c : ℕ → ℝ} {s κ : ℝ} (hs : 0 < s) (hκ : 0 < κ) (h1 : ∀ n, 0 < c n)
    (h2 : ∀ n : ℕ, κ * ((n : ℝ) + 1) ^ 2 ≤ c n ^ 6)
    (h3 : ∀ n m : ℕ, n ≠ m → s * |(n : ℝ) - m| ≤ |c n - c m| * (max (c n) (c m)) ^ 2) :
    ∃ K : ℝ, ∀ (t : ℝ) (N : ℕ),
      ∑ n ∈ range N, (1 / (4 * c n ^ 2)) ^ 2 / ((t - c n) ^ 2 + (1 / (4 * c n ^ 2)) ^ 2) ≤ K := by
  set Z : ℝ := ∑' k : ℤ, 1 / (k : ℝ) ^ 2 with hZ
  have hZs : Summable (fun k : ℤ => 1 / (k : ℝ) ^ 2) := Real.summable_one_div_int_pow.mpr (by norm_num)
  set W : ℝ := ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2 with hW
  have hWs : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
    have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
    simpa using this
  refine ⟨1 + 4 / s ^ 2 * Z + 1 / (4 * κ) * W, fun t N => ?_⟩
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp only [range_zero, sum_empty]
    have hZ0 : 0 ≤ Z := tsum_nonneg fun k => by positivity
    have hW0 : 0 ≤ W := tsum_nonneg fun k => by positivity
    positivity
  -- the nearest index
  obtain ⟨m, hmN, hmin⟩ := (range N).exists_min_image (fun n => |t - c n|) ⟨0, by simp [hN]⟩
  set φ : ℕ → ℤ := fun n => (n : ℤ) - m with hφ
  have hφinj : Function.Injective φ := fun a b h => by
    have : (a : ℤ) = b := by simpa [hφ] using h
    exact_mod_cast this
  -- the per-term bound
  have hterm : ∀ n ∈ range N, (1 / (4 * c n ^ 2)) ^ 2 / ((t - c n) ^ 2 + (1 / (4 * c n ^ 2)) ^ 2) ≤
      (if n = m then 1 else 0) + 4 / s ^ 2 * (1 / ((φ n : ℤ) : ℝ) ^ 2) + 1 / (4 * κ) * (1 / ((n : ℝ) + 1) ^ 2) := by
    intro n hn
    have hcn := h1 n
    have hr0 : 0 < 1 / (4 * c n ^ 2) := by positivity
    have hnonneg1 : 0 ≤ 4 / s ^ 2 * (1 / ((φ n : ℤ) : ℝ) ^ 2) := by positivity
    have hnonneg2 : 0 ≤ 1 / (4 * κ) * (1 / ((n : ℝ) + 1) ^ 2) := by positivity
    by_cases hnm : n = m
    · subst hnm
      simp only [ite_true]
      have := kernel_term_le_one (d := t - c n) hr0
      linarith
    · simp only [hnm, ite_false, zero_add]
      have hmin' : |t - c m| ≤ |t - c n| := hmin n hn
      have he : |c n - c m| ≤ 2 * |t - c n| := by
        have : c n - c m = (t - c m) - (t - c n) := by ring
        rw [this]
        calc |(t - c m) - (t - c n)| ≤ |t - c m| + |t - c n| := abs_sub _ _
          _ ≤ _ := by linarith
      have hsep := h3 n m hnm
      have hnm' : (0 : ℝ) < |(n : ℝ) - m| := abs_pos.mpr (by
        intro h; apply hnm; exact_mod_cast sub_eq_zero.mp h)
      have hmax : 0 < (max (c n) (c m)) ^ 2 := by have := h1 n; positivity
      have he0 : 0 < |c n - c m| := by
        by_contra h
        have : |c n - c m| = 0 := le_antisymm (not_lt.mp h) (abs_nonneg _)
        rw [this, zero_mul] at hsep
        nlinarith [mul_pos hs hnm']
      have hd : 0 < |t - c n| := by linarith
      have hk := kernel_term_le hcn (d := |t - c n|) hd
      rw [← sq_abs (t - c n)]
      refine hk.trans ?_
      by_cases hcase : c m ≤ 2 * c n
      · -- case A
        have hmx : max (c n) (c m) ≤ 2 * c n := max_le (by linarith) hcase
        have hmx2 : (max (c n) (c m)) ^ 2 ≤ 4 * c n ^ 2 := by nlinarith [le_max_left (c n) (c m)]
        have hA : s * |(n : ℝ) - m| ≤ |c n - c m| * (4 * c n ^ 2) :=
          hsep.trans (mul_le_mul_of_nonneg_left hmx2 (abs_nonneg _))
        have hd2 : s * |(n : ℝ) - m| ≤ 8 * c n ^ 2 * |t - c n| := by nlinarith [sq_nonneg (c n)]
        have hj : ((φ n : ℤ) : ℝ) ^ 2 = |(n : ℝ) - m| ^ 2 := by
          simp [hφ]
        rw [hj]
        have hx : 0 < s * |(n : ℝ) - m| := by positivity
        have hsq : (s * |(n : ℝ) - m|) ^ 2 ≤ (8 * c n ^ 2 * |t - c n|) ^ 2 :=
          pow_le_pow_left₀ hx.le hd2 2
        have : 1 / (16 * c n ^ 4 * |t - c n| ^ 2) ≤ 4 / s ^ 2 * (1 / |(n : ℝ) - m| ^ 2) := by
          rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [hsq]
        have h5 : 0 ≤ 1 / (4 * κ) * (1 / ((n : ℝ) + 1) ^ 2) := hnonneg2
        linarith
      · -- case B
        push Not at hcase
        have hd3 : c n / 2 ≤ |t - c n| := by
          have : c n < |c n - c m| := by
            rw [abs_sub_comm]; rw [abs_of_pos (by linarith)]; linarith
          linarith
        have hc6 : κ * ((n : ℝ) + 1) ^ 2 ≤ c n ^ 6 := h2 n
        have : 1 / (16 * c n ^ 4 * |t - c n| ^ 2) ≤ 1 / (4 * κ) * (1 / ((n : ℝ) + 1) ^ 2) := by
          have hsq : (c n / 2) ^ 2 ≤ |t - c n| ^ 2 := pow_le_pow_left₀ (by positivity) hd3 2
          rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
          have : 16 * c n ^ 4 * (c n / 2) ^ 2 = 4 * c n ^ 6 := by ring
          nlinarith [mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ 16 * c n ^ 4),
            mul_pos (by positivity : (0 : ℝ) < 4) hκ]
        have h5 : 0 ≤ 4 / s ^ 2 * (1 / ((φ n : ℤ) : ℝ) ^ 2) := hnonneg1
        linarith
  refine (sum_le_sum hterm).trans ?_
  rw [sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum]
  have e1 : ∑ n ∈ range N, (if n = m then (1 : ℝ) else 0) ≤ 1 := by
    rw [sum_ite_eq' (range N) m (fun _ => (1 : ℝ))]
    split_ifs
    norm_num
  have e2 : ∑ n ∈ range N, 1 / ((φ n : ℤ) : ℝ) ^ 2 ≤ Z := by
    have : ∑ n ∈ range N, 1 / ((φ n : ℤ) : ℝ) ^ 2 =
        ∑ k ∈ (range N).image φ, 1 / (k : ℝ) ^ 2 := by
      rw [sum_image (fun a _ b _ h => hφinj h)]
    rw [this]
    exact hZs.sum_le_tsum _ (fun k _ => by positivity)
  have e3 : ∑ n ∈ range N, 1 / ((n : ℝ) + 1) ^ 2 ≤ W :=
    hWs.sum_le_tsum _ (fun k _ => by positivity)
  have hs2 : 0 ≤ 4 / s ^ 2 := by positivity
  have hk4 : 0 ≤ 1 / (4 * κ) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left e2 hs2, mul_le_mul_of_nonneg_left e3 hk4]

/-- info: 'FormalResearch.Hardy.separated_kernel_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Hardy.separated_kernel_sum

end FormalResearch.Hardy
