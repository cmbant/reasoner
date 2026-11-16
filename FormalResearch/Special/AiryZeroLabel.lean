module

public import FormalResearch.Special.AiryZeroOrder

/-!
# Labelling the far zeros: the `n`-th zero of `Ai` has phase `(n - 1/4)π`

Combines the ordered zeros `a_n` (`AiryZeroOrder`: `a_n` is the unique zero with `n - 1` zeros in `(a_n, 0]`) with the
location of the zeros far on the negative axis (`AiryAsymZeros`: every zero `-r²` with `r ≥ 2` is within
`(2/5) r^{-3}` of a point `(2/3) r³ = (k + 3/4)π`; exactly one zero in each window `|(2/3) r³ - (k + 3/4)π| < π/3`,
`k ≥ 2`) and the finite count `a_1 ∈ (-2.35, -2.33)`, `a_2 ∈ (-4.84, -4)`, `a_3 < -4.84`
(`AiryFirstZeros`).

**Theorem `airyZero_phase`** (DLMF 9.9.6 with explicit remainder, with the offsets checked):
for every `n ≥ 2`, with `y = -a_n`,
`|(2/3) y^{3/2} - (n - 1/4) π| ≤ (2/5) y^{-3/2}`
(variable `r = √y`: `airyZero_phase_r`, `|(2/3) r³ - (n - 1/4)π| ≤ (2/5)/r³`).

Proof: induction on `n`.  `n = 2`: `y ∈ (4, 4.84)` and the location theorem gives a label `k`, forced to be `1` by
the numerical range.  `n → n + 1` (`n ≥ 2`): the window-`n` zero lies to the left of `a_n` (its phase exceeds
that of `a_n` by more than `2π/3 - 0.05`), so it is `≤ a_{n+1}` (`airyZero_next`); this gives
`(2/3) r_{n+1}³ < (n + 3/4)π + π/3`; the label `j` of `a_{n+1}` therefore satisfies `n - 1 ≤ j ≤ n`, and `j = n - 1`
is impossible because the window of label `n - 1` contains one zero only (`n ≥ 3`) resp. `a_3 < -4.84` (`n = 2`).

The consequences `|a_n| ≍ n^{2/3}`, the gaps `a_n - a_{n+1} ≍ n^{-1/3}` and the separation are in `AiryZeroSpacing`.

Numerically checked (mpmath, 30 digits, `2 ≤ n ≤ 200`): `|(2/3)|a_n|^{3/2} - (n - 1/4)π| ≤ 0.0124` and
`|a_n|^{3/2}·|(2/3)|a_n|^{3/2} - (n - 1/4)π|` increases from `0.1026` (`n = 2`) to its limit `5/48 = 0.1041…`
(the `5/(48 t²)` correction of DLMF 9.9.18), far inside the proved constant `2/5`.  Everything here is proved;
DLMF 9.9.18's second term is not (see the handoff).
-/

@[expose] public section

open Set
open scoped Real

namespace FormalResearch.Special

/-- `ρ n = √(-a_n)`. -/
noncomputable def airyZeroRoot (n : ℕ) : ℝ := √(-airyZero n)

lemma airyZeroRoot_pos (n : ℕ) : 0 < airyZeroRoot n :=
  Real.sqrt_pos.mpr (neg_pos.mpr (airyZero_neg n))

lemma airyZero_eq_neg_root_sq (n : ℕ) : airyZero n = -(airyZeroRoot n) ^ 2 := by
  rw [airyZeroRoot, Real.sq_sqrt (neg_nonneg.mpr (airyZero_nonpos n))]; ring

lemma airyAi_neg_root_sq (n : ℕ) : airyAi (-(airyZeroRoot n) ^ 2) = 0 := by
  rw [← airyZero_eq_neg_root_sq]; exact airyAi_airyZero n

lemma airyZeroRoot_lt {n m : ℕ} (hn : 1 ≤ n) (h : n < m) : airyZeroRoot n < airyZeroRoot m :=
  Real.sqrt_lt_sqrt (neg_nonneg.mpr (airyZero_nonpos n)) (by linarith [airyZero_lt_of_lt hn h])

lemma two_lt_airyZeroRoot_two : 2 < airyZeroRoot 2 ∧ airyZeroRoot 2 < 2.2 := by
  obtain ⟨h1, h2⟩ := airyZero_two
  constructor
  · rw [airyZeroRoot, Real.lt_sqrt (by norm_num)]; norm_num; linarith
  · rw [airyZeroRoot, Real.sqrt_lt' (by norm_num)]; norm_num; linarith

lemma two_lt_airyZeroRoot {n : ℕ} (hn : 2 ≤ n) : 2 < airyZeroRoot n := by
  rcases hn.eq_or_lt with rfl | h
  · exact two_lt_airyZeroRoot_two.1
  · exact two_lt_airyZeroRoot_two.1.trans (airyZeroRoot_lt (by norm_num) h)

lemma airyZeroRoot_three_gt {n : ℕ} (hn : 3 ≤ n) : 2.2 < airyZeroRoot n := by
  have h3 := airyZero_three
  have : airyZero n ≤ airyZero 3 := by
    rcases hn.eq_or_lt with rfl | h
    · exact le_rfl
    · exact (airyZero_lt_of_lt (by norm_num) h).le
  rw [airyZeroRoot, Real.lt_sqrt (by norm_num)]; norm_num; linarith

lemma airyLab_int_lt {j N : ℤ} {c : ℝ} (h : ((j : ℝ) + 3 / 4) * π < ((N : ℝ) + 3 / 4) * π + c)
    (hc : c < π) : j < N + 1 := by
  by_contra hcon
  push Not at hcon
  have : ((N : ℝ) + 1) ≤ j := by exact_mod_cast hcon
  nlinarith [Real.pi_pos]

lemma airyLab_int_gt {j N : ℤ} {c : ℝ} (h : ((N : ℝ) + 3 / 4) * π - c < ((j : ℝ) + 3 / 4) * π)
    (hc : c < π) : N - 1 < j := by
  by_contra hcon
  push Not at hcon
  have : (j : ℝ) ≤ (N : ℝ) - 1 := by
    have : j ≤ N - 1 := by omega
    exact_mod_cast this
  nlinarith [Real.pi_pos]

/-- Base case: `a_2` has label `1`. -/
lemma airyZero_phase_base :
    |2 / 3 * airyZeroRoot 2 ^ 3 - (1 + 3 / 4) * π| ≤ 2 / 5 / airyZeroRoot 2 ^ 3 := by
  obtain ⟨h2, h22⟩ := two_lt_airyZeroRoot_two
  obtain ⟨k, hk⟩ := airy_zero_location_r h2.le (airyAi_neg_root_sq 2)
  set r := airyZeroRoot 2
  have hr3 : 8 < r ^ 3 := by nlinarith [pow_lt_pow_left₀ h2 (by norm_num) (by norm_num : 3 ≠ 0)]
  have hr3' : r ^ 3 < 10.648 := by
    have := pow_lt_pow_left₀ h22 (by linarith) (by norm_num : 3 ≠ 0)
    norm_num at this; linarith
  have hT : 2 / 5 / r ^ 3 ≤ 0.05 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hk' := (abs_le.mp (hk.trans hT))
  obtain ⟨hp1, hp2⟩ := airyFZ_pi_bounds
  have hk1 : k = 1 := by
    have hlt : (k : ℝ) < 2 := by
      by_contra hc; push Not at hc
      nlinarith [hk'.1, hk'.2]
    have hgt : (0 : ℝ) < k := by
      by_contra hc; push Not at hc
      nlinarith [hk'.1, hk'.2]
    have h1 : k < 2 := by exact_mod_cast hlt
    have h2' : 0 < k := by exact_mod_cast hgt
    omega
  subst hk1
  simpa using hk

/-- Induction step. -/
lemma airyZero_phase_step {m : ℕ} (hm : 1 ≤ m)
    (ih : |2 / 3 * airyZeroRoot (m + 1) ^ 3 - ((m : ℝ) + 3 / 4) * π| ≤ 2 / 5 / airyZeroRoot (m + 1) ^ 3) :
    |2 / 3 * airyZeroRoot (m + 2) ^ 3 - (((m + 1 : ℕ) : ℝ) + 3 / 4) * π| ≤
      2 / 5 / airyZeroRoot (m + 2) ^ 3 := by
  obtain ⟨hp1, hp2⟩ := airyFZ_pi_bounds
  set ρ := airyZeroRoot (m + 1) with hρ
  set σ := airyZeroRoot (m + 2) with hσ
  have hρ2 : 2 < ρ := two_lt_airyZeroRoot (by omega)
  have hρσ : ρ < σ := airyZeroRoot_lt (by omega) (by omega)
  have hσ2 : 2 < σ := hρ2.trans hρσ
  have hρ3 : 8 < ρ ^ 3 := by nlinarith [pow_lt_pow_left₀ hρ2 (by norm_num) (by norm_num : 3 ≠ 0)]
  have hσ3 : 8 < σ ^ 3 := by nlinarith [pow_lt_pow_left₀ hσ2 (by norm_num) (by norm_num : 3 ≠ 0)]
  have hTρ : 2 / 5 / ρ ^ 3 ≤ 0.05 := by rw [div_le_iff₀ (by positivity)]; nlinarith
  have hTσ : 2 / 5 / σ ^ 3 ≤ 0.05 := by rw [div_le_iff₀ (by positivity)]; nlinarith
  have ih' := abs_le.mp (ih.trans hTρ)
  -- window zero of label m + 1
  obtain ⟨r, ⟨hr0, hrw, hrz⟩, -⟩ := airy_zero_window_existsUnique_r (k := ((m + 1 : ℕ) : ℤ))
    (by push_cast; omega)
  push_cast at hrw
  have hrw' := abs_lt.mp hrw
  have hρr3 : ρ ^ 3 < r ^ 3 := by
    have : 2 / 3 * ρ ^ 3 < 2 / 3 * r ^ 3 := by
      nlinarith [hrw'.1, ih'.2]
    linarith
  have hρr : ρ < r := lt_of_pow_lt_pow_left₀ 3 hr0.le hρr3
  have hzlt : -r ^ 2 < airyZero (m + 1) := by
    rw [airyZero_eq_neg_root_sq]
    have := pow_lt_pow_left₀ hρr (airyZeroRoot_pos _).le (by norm_num : 2 ≠ 0)
    linarith
  have hnext := airyZero_next (n := m + 1) (by omega) hrz hzlt
  have hσr : σ ≤ r := by
    rw [airyZero_eq_neg_root_sq (m + 1 + 1)] at hnext
    have : σ ^ 2 ≤ r ^ 2 := by linarith
    exact le_of_sq_le_sq this hr0.le |> fun h => h
  have hσr3 : σ ^ 3 ≤ r ^ 3 := pow_le_pow_left₀ (airyZeroRoot_pos _).le hσr 3
  -- label of σ
  obtain ⟨j, hj⟩ := airy_zero_location_r hσ2.le (airyAi_neg_root_sq (m + 2))
  have hj' := abs_le.mp (hj.trans hTσ)
  have hjlt : j < (m + 1 : ℤ) + 1 := by
    refine airyLab_int_lt (N := ((m : ℤ) + 1)) (c := π / 3 + 0.05) ?_ (by linarith)
    push_cast at hrw' ⊢
    nlinarith [hj'.1, hrw'.2]
  have hjgt : (m : ℤ) - 1 < j := by
    refine airyLab_int_gt (N := (m : ℤ)) (c := 0.1) ?_ (by linarith)
    have : 2 / 3 * ρ ^ 3 < 2 / 3 * σ ^ 3 := by
      have := pow_lt_pow_left₀ hρσ (airyZeroRoot_pos _).le (by norm_num : 3 ≠ 0); linarith
    push_cast
    nlinarith [hj'.2, ih'.1]
  have hjn : j = (m : ℤ) + 1 := by
    have hcases : j = m ∨ j = (m : ℤ) + 1 := by omega
    rcases hcases with hjm | hjm
    · exfalso
      rcases Nat.lt_or_ge m 2 with hm2 | hm2
      · -- m = 1
        have : m = 1 := by omega
        subst this
        have h3 := airyZeroRoot_three_gt (n := 1 + 2) (by norm_num)
        have h33 : 10.648 < σ ^ 3 := by
          have := pow_lt_pow_left₀ h3 (by norm_num) (by norm_num : 3 ≠ 0)
          norm_num at this ⊢; linarith
        rw [hjm] at hj'
        push_cast at hj'
        nlinarith [hj'.2]
      · -- uniqueness of the zero in the window of label m ≥ 2
        obtain ⟨r', -, hu⟩ := airy_zero_window_existsUnique_r (k := (m : ℤ)) (by omega)
        have e1 := hu ρ ⟨airyZeroRoot_pos _, by
          have := lt_of_le_of_lt (abs_le.mpr ih') (by linarith : (0.05 : ℝ) < π / 3)
          push_cast; exact this, airyAi_neg_root_sq (m + 1)⟩
        have e2 := hu σ ⟨airyZeroRoot_pos _, by
          rw [hjm] at hj'
          have := lt_of_le_of_lt (abs_le.mpr hj') (by linarith : (0.05 : ℝ) < π / 3)
          exact this, airyAi_neg_root_sq (m + 2)⟩
        linarith
    · exact hjm
  rw [hjn] at hj
  push_cast at hj ⊢
  exact hj

/-- **The phase of the `n`-th zero** (variable `r = √(-a_n)`): for `n ≥ 2`,
`|(2/3) r³ - (n - 1/4)π| ≤ (2/5)/r³`. -/
theorem airyZero_phase_r {n : ℕ} (hn : 2 ≤ n) :
    |2 / 3 * airyZeroRoot n ^ 3 - ((n : ℝ) - 1 / 4) * π| ≤ 2 / 5 / airyZeroRoot n ^ 3 := by
  induction n, hn using Nat.le_induction with
  | base => have := airyZero_phase_base; convert this using 3; norm_num
  | succ n hn ih =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have ih' : |2 / 3 * airyZeroRoot (m + 1) ^ 3 - ((m : ℝ) + 3 / 4) * π| ≤
        2 / 5 / airyZeroRoot (m + 1) ^ 3 := by
      convert ih using 4; push_cast; ring
    have := airyZero_phase_step (by omega) ih'
    convert this using 4; push_cast; ring

/-- **DLMF 9.9.6 for the ordered zeros, with explicit remainder.** For `n ≥ 2`, with `y = -a_n = |a_n|`:
`|(2/3) y^{3/2} - (n - 1/4)π| ≤ (2/5) y^{-3/2}`. -/
theorem airyZero_phase {n : ℕ} (hn : 2 ≤ n) :
    |2 / 3 * (-airyZero n) ^ (3 / 2 : ℝ) - ((n : ℝ) - 1 / 4) * π| ≤
      2 / 5 * (-airyZero n) ^ (-(3 / 2) : ℝ) := by
  have hy : 0 < -airyZero n := neg_pos.mpr (airyZero_neg n)
  have h := airyZero_phase_r hn
  have e : (-airyZero n) ^ (3 / 2 : ℝ) = airyZeroRoot n ^ 3 := by
    rw [airyZeroRoot, sqrt_cube_eq_rpow hy]
  rw [e, Real.rpow_neg hy.le, e]
  convert h using 2
  field_simp

/-- info: 'FormalResearch.Special.airyZero_phase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyZero_phase

end FormalResearch.Special
