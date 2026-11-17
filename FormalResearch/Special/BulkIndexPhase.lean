module

public import Mathlib

/-!
# Bulk index, part 1: the integer part of a phase and the sign pattern `(-1)^n cos`

Pure real-variable lemmas used by `BulkIndexCount`.  For a real phase `θ` put

* `bixN θ = ⌊θ/π + 1/2⌋` (the number of zeros `(ν - 1/2) π` of `cos` that lie at or below `θ`, up to the origin),
* `bixPhi θ = θ - (bixN θ - 1/2) π ∈ [0, π)` (the position of `θ` after the last zero of `cos`).

Then `cos θ = (-1)^{bixN θ} sin (bixPhi θ)` with `sin (bixPhi θ) ≥ 0` (`bix_cos_eq`), so `cos θ` has the sign
`(-1)^{bixN θ}` as soon as `bixPhi θ` is not within `η` of `0` or `π` (`bix_sin_le`).

* `bix_pair`: if `2η < θ - θ'` and `θ - θ' + 2η < π` then `bixN θ - bixN θ' ∈ {0, 1}` and the two phases are not both
  within `η` of a zero of `cos`.
* `bix_triple`: if `θ₁ > θ₂ > θ₃` with both steps in `(2η, π - 2η)` and `θ₂` is within `η` of a zero of `cos`, then
  `bixN θ₁ - bixN θ₃ = 1`.

**Claim class: proved** (elementary).  Not formalised: nothing beyond the statements above.
-/

@[expose] public section

open Real

namespace FormalResearch.Special

/-- `⌊θ/π + 1/2⌋`. -/
noncomputable def bixN (θ : ℝ) : ℤ := ⌊θ / π + 1 / 2⌋

/-- `θ - (⌊θ/π + 1/2⌋ - 1/2) π`, the position of `θ` after the last zero of `cos`. -/
noncomputable def bixPhi (θ : ℝ) : ℝ := θ - ((bixN θ : ℝ) - 1 / 2) * π

theorem bixPhi_nonneg (θ : ℝ) : 0 ≤ bixPhi θ := by
  have h := Int.floor_le (θ / π + 1 / 2)
  unfold bixPhi bixN
  have hπ := Real.pi_pos
  have : (⌊θ / π + 1 / 2⌋ : ℝ) * π ≤ (θ / π + 1 / 2) * π := mul_le_mul_of_nonneg_right h hπ.le
  have e : (θ / π + 1 / 2) * π = θ + π / 2 := by field_simp
  nlinarith

theorem bixPhi_lt (θ : ℝ) : bixPhi θ < π := by
  have h := Int.lt_floor_add_one (θ / π + 1 / 2)
  unfold bixPhi bixN
  have hπ := Real.pi_pos
  have : (θ / π + 1 / 2) * π < ((⌊θ / π + 1 / 2⌋ : ℝ) + 1) * π := mul_lt_mul_of_pos_right h hπ
  have e : (θ / π + 1 / 2) * π = θ + π / 2 := by field_simp
  nlinarith

theorem bixN_eq_of {θ : ℝ} {p : ℤ} (h0 : 0 ≤ θ - ((p : ℝ) - 1 / 2) * π) (h1 : θ - ((p : ℝ) - 1 / 2) * π < π) :
    bixN θ = p := by
  unfold bixN
  rw [Int.floor_eq_iff]
  have hπ := Real.pi_pos
  constructor
  · rw [← sub_nonneg]
    have : θ / π + 1 / 2 - p = (θ - ((p : ℝ) - 1 / 2) * π) / π := by field_simp; ring
    rw [this]; exact div_nonneg h0 hπ.le
  · rw [← sub_pos]
    have : (p : ℝ) + 1 - (θ / π + 1 / 2) = (π - (θ - ((p : ℝ) - 1 / 2) * π)) / π := by field_simp; ring
    rw [this]; apply div_pos <;> linarith

theorem bix_cos_eq (θ : ℝ) : Real.cos θ = (-1 : ℝ) ^ (bixN θ) * Real.sin (bixPhi θ) := by
  have h : θ = (bixPhi θ - π / 2) + (bixN θ : ℝ) * π := by unfold bixPhi; ring
  conv_lhs => rw [h]
  rw [Real.cos_add_int_mul_pi, Real.cos_sub_pi_div_two]

theorem bix_neg_one_zpow_sq (n : ℤ) : ((-1 : ℝ) ^ n) * ((-1 : ℝ) ^ n) = 1 := by
  rcases Int.even_or_odd n with h | h
  · rw [h.neg_one_zpow]; norm_num
  · rw [h.neg_one_zpow]; norm_num

theorem bix_sin_nonneg (θ : ℝ) : 0 ≤ Real.sin (bixPhi θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (bixPhi_nonneg θ) (bixPhi_lt θ).le

/-- `sin φ ≤ sin η` for `φ ∈ [0, π)` and `0 < η < π/2` forces `φ ≤ η` or `φ ≥ π - η`. -/
theorem bix_sin_le {φ η : ℝ} (hη0 : 0 < η)
    (h : Real.sin φ ≤ Real.sin η) : φ ≤ η ∨ π - η ≤ φ := by
  by_contra hc
  simp only [not_or, not_le] at hc
  obtain ⟨h1, h2⟩ := hc
  have hπ := Real.pi_pos
  rcases le_or_gt φ (π / 2) with hp | hp
  · have := Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) hp h1
    linarith
  · have e : Real.sin φ = Real.sin (π - φ) := (Real.sin_pi_sub φ).symm
    have := Real.sin_lt_sin_of_lt_of_le_pi_div_two (x := η) (y := π - φ) (by linarith) (by linarith) (by linarith)
    linarith

theorem bix_floor_step {θ θ' : ℝ} (h0 : θ' ≤ θ) (h1 : θ - θ' < π) :
    bixN θ - bixN θ' = 0 ∨ bixN θ - bixN θ' = 1 := by
  have hπ := Real.pi_pos
  have a1 : bixN θ' ≤ bixN θ := by
    unfold bixN; apply Int.floor_le_floor; have : θ' / π ≤ θ / π := by gcongr
    linarith
  have a2 : bixN θ ≤ bixN θ' + 1 := by
    unfold bixN
    rw [← Int.floor_add_one]
    apply Int.floor_le_floor
    have : θ / π ≤ θ' / π + 1 := by
      rw [← sub_le_iff_le_add', ← sub_div, div_le_one hπ]; linarith
    linarith
  omega

/-- Two phases a step `d ∈ (2η, π - 2η)` apart: the integer parts differ by `0` or `1`, and at most one of them is
within `η` of a zero of `cos`. -/
theorem bix_pair {θ θ' η : ℝ} (hη0 : 0 < η) (hd1 : 2 * η < θ - θ') (hd2 : θ - θ' + 2 * η < π) :
    (bixN θ - bixN θ' = 0 ∨ bixN θ - bixN θ' = 1) ∧
      ¬ ((bixPhi θ ≤ η ∨ π - η ≤ bixPhi θ) ∧ (bixPhi θ' ≤ η ∨ π - η ≤ bixPhi θ')) := by
  have hπ := Real.pi_pos
  have hfl := bix_floor_step (θ := θ) (θ' := θ') (by linarith) (by linarith)
  refine ⟨hfl, ?_⟩
  have rel : bixPhi θ - bixPhi θ' = (θ - θ') - ((bixN θ - bixN θ' : ℤ) : ℝ) * π := by
    unfold bixPhi; push_cast; ring
  have p1 := bixPhi_nonneg θ
  have p2 := bixPhi_lt θ
  have p3 := bixPhi_nonneg θ'
  have p4 := bixPhi_lt θ'
  rcases hfl with h | h
  · rw [h] at rel; push_cast at rel
    rintro ⟨h1 | h1, h2 | h2⟩ <;> nlinarith
  · rw [h] at rel; push_cast at rel
    rintro ⟨h1 | h1, h2 | h2⟩ <;> nlinarith

/-- A phase `θ₂` within `η` of a zero of `cos` between two phases at distance in `(2η, π - 2η)`: the integer parts of the
outer phases differ by exactly `1`. -/
theorem bix_triple {θ₁ θ₂ θ₃ η : ℝ} (hη0 : 0 < η) (hd1 : 2 * η < θ₁ - θ₂) (hd1' : θ₁ - θ₂ + 2 * η < π)
    (hd2 : 2 * η < θ₂ - θ₃) (hd2' : θ₂ - θ₃ + 2 * η < π) (hi : bixPhi θ₂ ≤ η ∨ π - η ≤ bixPhi θ₂) :
    bixN θ₁ - bixN θ₃ = 1 := by
  have hπ := Real.pi_pos
  have p1 := bixPhi_nonneg θ₂
  have p2 := bixPhi_lt θ₂
  have e : θ₂ = bixPhi θ₂ + ((bixN θ₂ : ℝ) - 1 / 2) * π := by unfold bixPhi; ring
  rcases hi with h | h
  · have n1 : bixN θ₁ = bixN θ₂ := bixN_eq_of (by nlinarith) (by nlinarith)
    have n3 : bixN θ₃ = bixN θ₂ - 1 := bixN_eq_of (by push_cast; nlinarith) (by push_cast; nlinarith)
    omega
  · have n1 : bixN θ₁ = bixN θ₂ + 1 := bixN_eq_of (by push_cast; nlinarith) (by push_cast; nlinarith)
    have n3 : bixN θ₃ = bixN θ₂ := bixN_eq_of (by nlinarith) (by nlinarith)
    omega

end FormalResearch.Special
