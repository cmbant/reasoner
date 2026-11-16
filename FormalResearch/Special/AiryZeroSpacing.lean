module

public import FormalResearch.Special.AiryZeroLabel

/-!
# Size and spacing of the ordered zeros of `Ai`

From the phase theorem `airyZero_phase_r` (`|(2/3) ρ_n³ - (n - 1/4)π| ≤ (2/5)/ρ_n³ ≤ 1/20`, `ρ_n = √|a_n|`,
`n ≥ 2`) one gets, with explicit constants (all for `n ≥ 2` unless stated):

* `airyZero_cube_bounds`: `4.08 n ≤ |a_n|^{3/2} ≤ 4.72 n`, equivalently `16 n² ≤ |a_n|³ ≤ 23 n²`
  (`airyZero_abs_cube_bounds`), and `2.5 n^{2/3} ≤ |a_n| ≤ 2.85 n^{2/3}` (`airyZero_abs_bounds`): **`|a_n| ≍ n^{2/3}`**;
* `airyZero_gap_cube_bounds`: the gaps `g_n = a_n - a_{n+1}` satisfy `5.9 ≤ (n + 1) g_n³` and `n g_n³ ≤ 8.4`;
  `airyZero_gap_bounds`: **`1.8 (n+1)^{-1/3} ≤ a_n - a_{n+1} ≤ 2.05 n^{-1/3}`** — from
  `(2/3)Δ/ρ_{n+1} ≤ g_n ≤ (2/3)Δ/ρ_n` with `Δ = ρ_{n+1}³ - ρ_n³ ∈ [4.56, 4.87]` (`airyZero_gap_between`);
* `airyZero_separation`: for `2 ≤ k < n`, `1.8 (n - k) n^{-1/3} ≤ a_k - a_n ≤ 2.05 (n - k) k^{-1/3}`;
  `airyZero_separation_lower`, `airyZero_abs_sub_ge`: **`|a_n - a_k| ≥ 1.8 |n - k| max(n,k)^{-1/3}`** for all `n ≠ k`,
  `n, k ≥ 1` (the case `k = 1` uses `a_1 - a_2 > 1.65` from `AiryFirstZeros`).

Numerically checked with mpmath (30 digits) for `n ≤ 62` (and all pairs `2 ≤ k < n ≤ 62` for the separation):
`|a_n|^{3/2}/n ∈ [4.08, 4.72]`, `|a_n|/n^{2/3} ∈ [2.5, 2.85]`, `g_n n^{1/3} ∈ [1.8049, 1.8713]`,
`Δ_n ∈ [4.56, 4.87]`.  The constants are not optimal (the true limits are `|a_n|/n^{2/3} → (3π/2)^{2/3} = 2.8108…` and
`g_n n^{1/3} → (2/3)(3π/2)^{2/3} = 1.8739…`).  Everything proved.
-/

@[expose] public section

open Set
open scoped Real

namespace FormalResearch.Special

/-- Phase estimate in the weak form `|(2/3) ρ_n³ - (n - 1/4)π| ≤ 1/20`. -/
lemma airyZero_phase_weak {n : ℕ} (hn : 2 ≤ n) :
    |2 / 3 * airyZeroRoot n ^ 3 - ((n : ℝ) - 1 / 4) * π| ≤ 1 / 20 := by
  have h := airyZero_phase_r hn
  have h2 := two_lt_airyZeroRoot hn
  have : 8 < airyZeroRoot n ^ 3 := by
    nlinarith [pow_lt_pow_left₀ h2 (by norm_num) (by norm_num : 3 ≠ 0)]
  refine h.trans ?_
  rw [div_le_iff₀ (by positivity)]; nlinarith

/-- **`|a_n|^{3/2} ≍ n`**: `4.08 n ≤ ρ_n³ ≤ 4.72 n`. -/
theorem airyZero_cube_bounds {n : ℕ} (hn : 2 ≤ n) :
    4.08 * n ≤ airyZeroRoot n ^ 3 ∧ airyZeroRoot n ^ 3 ≤ 4.72 * n := by
  have h := abs_le.mp (airyZero_phase_weak hn)
  obtain ⟨hp1, hp2⟩ := airyFZ_pi_bounds
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  constructor <;> nlinarith [h.1, h.2]

lemma airyZeroRoot_six (n : ℕ) : (-airyZero n) ^ 3 = (airyZeroRoot n ^ 3) ^ 2 := by
  rw [airyZero_eq_neg_root_sq n, neg_neg]; ring

/-- `16 n² ≤ |a_n|³ ≤ 23 n²` for `n ≥ 2`. -/
theorem airyZero_abs_cube_bounds {n : ℕ} (hn : 2 ≤ n) :
    16 * (n : ℝ) ^ 2 ≤ (-airyZero n) ^ 3 ∧ (-airyZero n) ^ 3 ≤ 23 * (n : ℝ) ^ 2 := by
  obtain ⟨h1, h2⟩ := airyZero_cube_bounds hn
  rw [airyZeroRoot_six]
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  constructor <;> nlinarith

lemma airyRpow_cube (c N : ℝ) (hN : 0 < N) : (c * N ^ (-(1 / 3) : ℝ)) ^ 3 = c ^ 3 / N := by
  have h : (N ^ (-(1 / 3) : ℝ)) ^ 3 = N ^ (-1 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]; norm_num
  rw [mul_pow, h, Real.rpow_neg_one, div_eq_mul_inv]

lemma airyRpow_le_of_cube {g c N : ℝ} (hg : 0 < g) (hN : 0 < N) (h : c ^ 3 ≤ g ^ 3 * N) :
    c * N ^ (-(1 / 3) : ℝ) ≤ g := by
  refine le_of_pow_le_pow_left₀ (by norm_num : 3 ≠ 0) hg.le ?_
  rw [airyRpow_cube c N hN, div_le_iff₀ hN]; linarith

lemma airyRpow_ge_of_cube {g C N : ℝ} (hC : 0 < C) (hN : 0 < N) (h : g ^ 3 * N ≤ C ^ 3) :
    g ≤ C * N ^ (-(1 / 3) : ℝ) := by
  refine le_of_pow_le_pow_left₀ (by norm_num : 3 ≠ 0) (by positivity) ?_
  rw [airyRpow_cube C N hN, le_div_iff₀ hN]; linarith

/-- `2.5 n^{2/3} ≤ |a_n| ≤ 2.85 n^{2/3}` for `n ≥ 2`. -/
theorem airyZero_abs_bounds {n : ℕ} (hn : 2 ≤ n) :
    2.5 * (n : ℝ) ^ (2 / 3 : ℝ) ≤ -airyZero n ∧ -airyZero n ≤ 2.85 * (n : ℝ) ^ (2 / 3 : ℝ) := by
  obtain ⟨h1, h2⟩ := airyZero_abs_cube_bounds hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hy : 0 < -airyZero n := neg_pos.mpr (airyZero_neg n)
  have hc : ((n : ℝ) ^ (2 / 3 : ℝ)) ^ 3 = (n : ℝ) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]; norm_num
  have hp : 0 < (n : ℝ) ^ (2 / 3 : ℝ) := by positivity
  constructor
  · refine le_of_pow_le_pow_left₀ (by norm_num : 3 ≠ 0) hy.le ?_
    rw [mul_pow, hc]; nlinarith
  · refine le_of_pow_le_pow_left₀ (by norm_num : 3 ≠ 0) (by positivity) ?_
    rw [mul_pow, hc]; nlinarith

/-- The gap lies between `(2/3)Δ/ρ_{n+1}` and `(2/3)Δ/ρ_n`, `Δ = ρ_{n+1}³ - ρ_n³`. -/
theorem airyZero_gap_between {n : ℕ} (hn : 1 ≤ n) :
    2 / 3 * (airyZeroRoot (n + 1) ^ 3 - airyZeroRoot n ^ 3) ≤
        (airyZero n - airyZero (n + 1)) * airyZeroRoot (n + 1) ∧
      (airyZero n - airyZero (n + 1)) * airyZeroRoot n ≤
        2 / 3 * (airyZeroRoot (n + 1) ^ 3 - airyZeroRoot n ^ 3) := by
  have hρ := airyZeroRoot_pos n
  have hσ := airyZeroRoot_pos (n + 1)
  have hlt := airyZeroRoot_lt hn (Nat.lt_succ_self n)
  set ρ := airyZeroRoot n
  set σ := airyZeroRoot (n + 1)
  rw [airyZero_eq_neg_root_sq n, airyZero_eq_neg_root_sq (n + 1)]
  have hd : 0 ≤ σ - ρ := by linarith
  constructor
  · nlinarith [mul_nonneg (sq_nonneg (σ - ρ)) (by linarith : 0 ≤ σ + 2 * ρ)]
  · nlinarith [mul_nonneg (sq_nonneg (σ - ρ)) (by linarith : 0 ≤ 2 * σ + ρ)]

/-- `Δ_n = ρ_{n+1}³ - ρ_n³ ∈ [4.56, 4.87]`. -/
lemma airyZero_delta_bounds {n : ℕ} (hn : 2 ≤ n) :
    4.56 ≤ airyZeroRoot (n + 1) ^ 3 - airyZeroRoot n ^ 3 ∧
      airyZeroRoot (n + 1) ^ 3 - airyZeroRoot n ^ 3 ≤ 4.87 := by
  have h1 := abs_le.mp (airyZero_phase_weak hn)
  have h2 := abs_le.mp (airyZero_phase_weak (by omega : 2 ≤ n + 1))
  obtain ⟨hp1, hp2⟩ := airyFZ_pi_bounds
  push_cast at h2
  constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]

/-- **Cubic form of the gap bounds**: `5.9 ≤ (n + 1) g_n³` and `n g_n³ ≤ 8.4`, `g_n = a_n - a_{n+1}`. -/
theorem airyZero_gap_cube_bounds {n : ℕ} (hn : 2 ≤ n) :
    5.9 ≤ ((n : ℝ) + 1) * (airyZero n - airyZero (n + 1)) ^ 3 ∧
      (n : ℝ) * (airyZero n - airyZero (n + 1)) ^ 3 ≤ 8.4 := by
  obtain ⟨hb1, hb2⟩ := airyZero_gap_between (by omega : 1 ≤ n)
  obtain ⟨hd1, hd2⟩ := airyZero_delta_bounds hn
  obtain ⟨hc1, hc2⟩ := airyZero_cube_bounds hn
  obtain ⟨hc3, hc4⟩ := airyZero_cube_bounds (by omega : 2 ≤ n + 1)
  push_cast at hc3 hc4
  have hρ := airyZeroRoot_pos n
  have hσ := airyZeroRoot_pos (n + 1)
  have hg : 0 < airyZero n - airyZero (n + 1) := by
    have := airyZero_strictAnti (by omega : 1 ≤ n); linarith
  set g := airyZero n - airyZero (n + 1)
  set ρ := airyZeroRoot n
  set σ := airyZeroRoot (n + 1)
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  constructor
  · -- 3.04 ≤ g σ, so 28.09 ≤ g³ σ³ ≤ g³ · 4.72 (n+1)
    have h1 : 3.04 ≤ g * σ := by linarith
    have h2 : 3.04 ^ 3 ≤ (g * σ) ^ 3 := pow_le_pow_left₀ (by norm_num) h1 3
    rw [mul_pow] at h2
    have h3 : g ^ 3 * σ ^ 3 ≤ g ^ 3 * (4.72 * ((n : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left hc4 (by positivity)
    nlinarith
  · -- g ρ ≤ 3.2467, so g³ ρ³ ≤ 34.22 and ρ³ ≥ 4.08 n
    have h1 : g * ρ ≤ 3.247 := by linarith
    have h2 : (g * ρ) ^ 3 ≤ 3.247 ^ 3 := pow_le_pow_left₀ (by positivity) h1 3
    rw [mul_pow] at h2
    have h3 : g ^ 3 * (4.08 * (n : ℝ)) ≤ g ^ 3 * ρ ^ 3 :=
      mul_le_mul_of_nonneg_left hc1 (by positivity)
    nlinarith

/-- **Gaps between consecutive zeros** (DLMF 9.9.6 consequence): for `n ≥ 2`,
`1.8 (n+1)^{-1/3} ≤ a_n - a_{n+1} ≤ 2.05 n^{-1/3}`. -/
theorem airyZero_gap_bounds {n : ℕ} (hn : 2 ≤ n) :
    1.8 * ((n : ℝ) + 1) ^ (-(1 / 3) : ℝ) ≤ airyZero n - airyZero (n + 1) ∧
      airyZero n - airyZero (n + 1) ≤ 2.05 * (n : ℝ) ^ (-(1 / 3) : ℝ) := by
  obtain ⟨h1, h2⟩ := airyZero_gap_cube_bounds hn
  have hg : 0 < airyZero n - airyZero (n + 1) := by
    have := airyZero_strictAnti (by omega : 1 ≤ n); linarith
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  constructor
  · refine airyRpow_le_of_cube hg (by positivity) ?_
    nlinarith
  · refine airyRpow_ge_of_cube (by norm_num) hn' ?_
    nlinarith

/-- **Separation of the zeros**: for `2 ≤ k < n`,
`1.8 (n - k) n^{-1/3} ≤ a_k - a_n ≤ 2.05 (n - k) k^{-1/3}`; in particular
`|a_n - a_k| ≥ 1.8 |n - k| max(n,k)^{-1/3}` (the case `n < k` is the same statement with the roles exchanged). -/
theorem airyZero_separation {k n : ℕ} (hk : 2 ≤ k) (hkn : k < n) :
    1.8 * ((n : ℝ) - k) * (n : ℝ) ^ (-(1 / 3) : ℝ) ≤ airyZero k - airyZero n ∧
      airyZero k - airyZero n ≤ 2.05 * ((n : ℝ) - k) * (k : ℝ) ^ (-(1 / 3) : ℝ) := by
  induction n, hkn using Nat.le_induction with
  | base =>
    obtain ⟨h1, h2⟩ := airyZero_gap_bounds hk
    have e : ((k + 1 : ℕ) : ℝ) - k = 1 := by push_cast; ring
    rw [e]
    push_cast
    constructor <;> linarith
  | succ n hn ih =>
    obtain ⟨ih1, ih2⟩ := ih
    obtain ⟨h1, h2⟩ := airyZero_gap_bounds (by omega : 2 ≤ n)
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    have hkn' : (k : ℝ) ≤ n := by exact_mod_cast (by omega : k ≤ n)
    have hmono : ((n : ℝ) + 1) ^ (-(1 / 3) : ℝ) ≤ (n : ℝ) ^ (-(1 / 3) : ℝ) :=
      Real.rpow_le_rpow_of_nonpos hn0 (by linarith) (by norm_num)
    have hmono2 : (n : ℝ) ^ (-(1 / 3) : ℝ) ≤ (k : ℝ) ^ (-(1 / 3) : ℝ) :=
      Real.rpow_le_rpow_of_nonpos hk0 hkn' (by norm_num)
    push_cast
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left hmono (by nlinarith : (0 : ℝ) ≤ 1.8 * ((n : ℝ) - k))]
    · nlinarith [mul_le_mul_of_nonneg_left hmono2 (by norm_num : (0 : ℝ) ≤ 2.05)]

/-- **Separation including `a_1`**: for `1 ≤ k < n`, `a_k - a_n ≥ 1.8 (n - k) n^{-1/3}`; with the symmetric case,
`|a_n - a_k| ≥ 1.8 |n - k| max(n,k)^{-1/3}` for all `n ≠ k` (`n, k ≥ 1`). -/
theorem airyZero_separation_lower {k n : ℕ} (hk : 1 ≤ k) (hkn : k < n) :
    1.8 * ((n : ℝ) - k) * (n : ℝ) ^ (-(1 / 3) : ℝ) ≤ airyZero k - airyZero n := by
  rcases Nat.lt_or_ge 1 k with hk2 | hk1
  · exact (airyZero_separation (by omega) hkn).1
  · have hk' : k = 1 := by omega
    subst hk'
    have hn2 : 2 ≤ n := hkn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    obtain ⟨-, h1, -, h2, -⟩ := airyZero_first_values
    have hpow : (n : ℝ) ^ (-(1 / 3) : ℝ) ≤ 0.8 := by
      have h2n : (2 : ℝ) ≤ n := by exact_mod_cast hn2
      have := Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 2) h2n (by norm_num : -(1 / 3 : ℝ) ≤ 0)
      refine this.trans ?_
      refine le_of_pow_le_pow_left₀ (by norm_num : 3 ≠ 0) (by norm_num) ?_
      rw [show ((2 : ℝ) ^ (-(1 / 3) : ℝ)) ^ 3 = 1 / 2 by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num]
      norm_num
    have hpos : 0 < (n : ℝ) ^ (-(1 / 3) : ℝ) := by positivity
    have h12 : airyZero 1 - airyZero 2 ≥ 1.65 := by
      obtain ⟨h1', -⟩ := airyZero_one
      obtain ⟨-, h2'⟩ := airyZero_two
      linarith
    rcases Nat.lt_or_ge 2 n with hn3 | hn3
    · have := (airyZero_separation (k := 2) (n := n) le_rfl hn3).1
      push_cast at this ⊢
      nlinarith
    · have hn : n = 2 := by omega
      subst hn
      push_cast
      nlinarith

/-- **`|a_n - a_k| ≥ 1.8 |n - k| max(n,k)^{-1/3}`** for all `n ≠ k`, `n, k ≥ 1`. -/
theorem airyZero_abs_sub_ge {k n : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) (hne : k ≠ n) :
    1.8 * |(n : ℝ) - k| * ((max n k : ℕ) : ℝ) ^ (-(1 / 3) : ℝ) ≤ |airyZero n - airyZero k| := by
  rcases lt_or_gt_of_ne hne with h | h
  · have h1 := airyZero_separation_lower hk h
    have hkn : (k : ℝ) < n := by exact_mod_cast h
    have h3 := airyZero_lt_of_lt hk h
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ (n : ℝ) - k), abs_sub_comm,
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ airyZero k - airyZero n), max_eq_left h.le]
    exact h1
  · have h1 := airyZero_separation_lower hn h
    have hkn : (n : ℝ) < k := by exact_mod_cast h
    have h3 := airyZero_lt_of_lt hn h
    rw [abs_sub_comm, abs_of_nonneg (by linarith : (0 : ℝ) ≤ (k : ℝ) - n),
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ airyZero n - airyZero k), max_eq_right h.le]
    exact h1

/-- info: 'FormalResearch.Special.airyZero_gap_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyZero_gap_bounds

/-- info: 'FormalResearch.Special.airyZero_separation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyZero_separation

/-- info: 'FormalResearch.Special.airyZero_abs_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyZero_abs_bounds

/-- info: 'FormalResearch.Special.airyZero_abs_sub_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyZero_abs_sub_ge

end FormalResearch.Special
