module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremB.ThbGeom

/-!
# Paper J, Theorem B, L3.5c, part 9: lattice geometry of the rows of the two soft charts (pure real arithmetic)

Source: Paper J `app_thmB.tex`, proof of `prop:thb-inputs`, the rows of the soft halves: the left half is the collar rows `a + 1 .. n_c` (`a = floor((u_c - eta/2)/h - 1/2)`, the last row below the collar), the right half the rows `g_0 .. b - 1`
(`b = ceil((u_c + eta/2)/h - 1/2)`, the first row above the collar), where `n_c = nearestRow u_c` and `g_0 = N - nearestRow (L - u_c)` is the global row of the fold row of the mirror chain; `g_0 <= n_c <= g_0 + 1` and both rows are within `h/2` of `u_c`.

## Proved here

* `nearestRow_eq_floor`: `nearestRow h x = floor(x/h)` (round half up).
* `soft_geom`: for `0 < h <= eta/4`, `h (N+1) = L`, `0 < u_c - 2 eta`, `u_c + 2 eta < L`: `0 <= a`, `a + 1 <= n_c`, `g_0 <= n_c <= g_0 + 1`, `g_0 + 1 <= b <= N`, `|u_{g_0} - u_c| <= h/2`, `|u_{n_c} - u_c| <= h/2`, and the node facts of the rows of both charts and of the rows outside them.

## Differences from the paper

The right half starts at `g_0` (one row before the splice row `n_c + 1` in the tie case `u_c/h in Z`) so that the half-window of the mirror chart `{chain row <= nearestRow (L - u_c)}` is covered; the rows `g_0 .. n_c` are not used by `hat G`.

## Not formalised

Nothing.
-/

@[expose] public section

namespace FormalResearch.JacobiEigenvectors.TheoremB

open FormalResearch.JacobiEigenvectors.Setting

theorem nearestRow_eq_floor (h x : ℝ) : nearestRow h x = ⌊x / h⌋ := by
  unfold nearestRow
  rw [round_eq]
  congr 1
  ring

/-- The geometry of the soft rows. -/
theorem soft_geom {h uc η L : ℝ} {N : ℕ} (hh : 0 < h) (hη : 0 < η) (hsm : h ≤ η / 4) (hL : h * ((N : ℝ) + 1) = L)
    (hu1 : 0 < uc - 2 * η) (hu2 : uc + 2 * η < L) :
    0 ≤ ⌊(uc - η / 2) / h - 1 / 2⌋ ∧
    ⌊(uc - η / 2) / h - 1 / 2⌋ + 1 ≤ nearestRow h uc ∧
    N - nearestRow h (L - uc) ≤ nearestRow h uc ∧ nearestRow h uc ≤ N - nearestRow h (L - uc) + 1 ∧
    |uNode h (N - nearestRow h (L - uc)) - uc| ≤ h / 2 ∧ |uNode h (nearestRow h uc) - uc| ≤ h / 2 ∧
    N - nearestRow h (L - uc) + 1 ≤ ⌈(uc + η / 2) / h - 1 / 2⌉ ∧ ⌈(uc + η / 2) / h - 1 / 2⌉ + 1 ≤ N ∧
    0 ≤ N - nearestRow h (L - uc) ∧
    (∀ i : ℤ, ⌊(uc - η / 2) / h - 1 / 2⌋ + 1 ≤ i → uc - η / 2 < uNode h i) ∧
    (∀ i : ℤ, i ≤ ⌊(uc - η / 2) / h - 1 / 2⌋ → uNode h i ≤ uc - η / 2) ∧
    (∀ i : ℤ, i < ⌈(uc + η / 2) / h - 1 / 2⌉ → uNode h i < uc + η / 2) ∧
    (∀ i : ℤ, ⌈(uc + η / 2) / h - 1 / 2⌉ ≤ i → uc + η / 2 ≤ uNode h i) ∧
    (∀ i : ℤ, i ≤ nearestRow h uc → uNode h i ≤ uc + h / 2) ∧ nearestRow h uc + 1 ≤ N := by
  have hx : ∀ i : ℤ, uNode h i = ((i : ℝ) + 1 / 2) * h := fun i => rfl
  set x : ℝ := uc / h with hxdef
  have hxh : x * h = uc := by rw [hxdef]; field_simp
  have hLx : (L - uc) / h = (N : ℝ) + 1 - x := by
    rw [← hL, hxdef]; field_simp
  have hnc : (nearestRow h uc : ℝ) ≤ x ∧ x < (nearestRow h uc : ℝ) + 1 := by
    rw [nearestRow_eq_floor]; exact ⟨Int.floor_le _, Int.lt_floor_add_one _⟩
  have hncR : (nearestRow h (L - uc) : ℝ) ≤ (N : ℝ) + 1 - x ∧ (N : ℝ) + 1 - x < (nearestRow h (L - uc) : ℝ) + 1 := by
    rw [nearestRow_eq_floor, hLx.symm]; exact ⟨Int.floor_le _, Int.lt_floor_add_one _⟩
  set nc := nearestRow h uc with hncdef
  set g0 : ℤ := (N : ℤ) - nearestRow h (L - uc) with hg0
  have hg0r : x - 1 ≤ (g0 : ℝ) ∧ (g0 : ℝ) < x := by
    have : (g0 : ℝ) = (N : ℝ) - (nearestRow h (L - uc) : ℝ) := by rw [hg0]; push_cast; ring
    rw [this]; constructor <;> linarith [hncR.1, hncR.2]
  have hηh : 4 * h ≤ η := by linarith
  -- the collar bounds
  have hy : (uc - η / 2) / h - 1 / 2 = x - η / (2 * h) - 1 / 2 := by rw [hxdef]; field_simp
  have hηx : 2 ≤ η / (2 * h) := by rw [le_div_iff₀ (by positivity)]; linarith
  have hxpos : 3 / 2 ≤ x - η / (2 * h) := by
    have : (2 * η) ≤ uc := by linarith
    have h3 : 2 * η / h ≤ x := by rw [hxdef]; exact div_le_div_of_nonneg_right this hh.le
    have h4 : 2 * η / h = 4 * (η / (2 * h)) := by field_simp; ring
    linarith
  set a : ℤ := ⌊(uc - η / 2) / h - 1 / 2⌋ with hadef
  have ha1 : (a : ℝ) ≤ (uc - η / 2) / h - 1 / 2 := Int.floor_le _
  have ha2 : (uc - η / 2) / h - 1 / 2 < (a : ℝ) + 1 := Int.lt_floor_add_one _
  set b : ℤ := ⌈(uc + η / 2) / h - 1 / 2⌉ with hbdef
  have hb1 : (uc + η / 2) / h - 1 / 2 ≤ (b : ℝ) := Int.le_ceil _
  have hb2 : (b : ℝ) < (uc + η / 2) / h - 1 / 2 + 1 := Int.ceil_lt_add_one _
  have hy2 : (uc + η / 2) / h - 1 / 2 = x + η / (2 * h) - 1 / 2 := by rw [hxdef]; field_simp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : (0 : ℝ) ≤ (uc - η / 2) / h - 1 / 2 := by rw [hy]; linarith
    exact Int.floor_nonneg.mpr this
  · have : (a : ℝ) + 1 ≤ (nc : ℝ) := by
      rw [hy] at ha1; linarith
    have h2 : a + 1 ≤ nc := by exact_mod_cast this
    exact h2
  · have : (g0 : ℝ) < (nc : ℝ) + 1 := by linarith [hg0r.2, hnc.2]
    have : g0 < nc + 1 := by exact_mod_cast this
    omega
  · have : (nc : ℝ) < (g0 : ℝ) + 1 + 1 := by linarith [hg0r.1, hnc.1]
    have : nc < g0 + 1 + 1 := by exact_mod_cast this
    omega
  · rw [hx, abs_le]; constructor <;> nlinarith [hg0r.1, hg0r.2]
  · rw [hx, abs_le]; constructor <;> nlinarith [hnc.1, hnc.2]
  · have : (g0 : ℝ) + 1 ≤ (b : ℝ) := by rw [hy2] at hb1; linarith [hg0r.2]
    exact_mod_cast this
  · have : (b : ℝ) + 1 ≤ (N : ℝ) := by
      -- b < x + eta/(2h) + 1/2, and x + eta/(2h) + 1/2 + 1 <= N
      have hh2 : (uc + η / 2) / h + 1 / 2 + 1 ≤ (N : ℝ) := by
        rw [← sub_nonneg]
        have : (N : ℝ) - ((uc + η / 2) / h + 1 / 2 + 1) = (L - uc - η / 2 - 3 * h / 2 - h) / h + 0 := by
          rw [← hL]; field_simp; ring
        have h5 : 0 ≤ (L - uc - η / 2 - 3 * h / 2 - h) / h := by
          apply div_nonneg _ hh.le; linarith
        linarith
      linarith
    exact_mod_cast this
  · have : (0 : ℝ) ≤ (g0 : ℝ) := by
      -- g0 >= x - 1 >= 1/2
      have : 3 / 2 ≤ x := by linarith [hηx]
      linarith [hg0r.1]
    exact_mod_cast this
  · intro i hi
    have : (a : ℝ) + 1 ≤ (i : ℝ) := by exact_mod_cast hi
    rw [hx]
    have h1 : (uc - η / 2) / h < (i : ℝ) + 1 / 2 := by linarith
    have := mul_lt_mul_of_pos_right h1 hh
    rwa [div_mul_cancel₀ _ hh.ne'] at this
  · intro i hi
    have : (i : ℝ) ≤ (a : ℝ) := by exact_mod_cast hi
    rw [hx]
    have h1 : (i : ℝ) + 1 / 2 ≤ (uc - η / 2) / h := by linarith
    have := mul_le_mul_of_nonneg_right h1 hh.le
    rwa [div_mul_cancel₀ _ hh.ne'] at this
  · intro i hi
    have : (i : ℝ) + 1 ≤ (b : ℝ) := by exact_mod_cast hi
    rw [hx]
    have h1 : (i : ℝ) + 1 / 2 < (uc + η / 2) / h := by linarith
    have := mul_lt_mul_of_pos_right h1 hh
    rwa [div_mul_cancel₀ _ hh.ne'] at this
  · intro i hi
    have : (b : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
    rw [hx]
    have h1 : (uc + η / 2) / h ≤ (i : ℝ) + 1 / 2 := by linarith
    have := mul_le_mul_of_nonneg_right h1 hh.le
    rwa [div_mul_cancel₀ _ hh.ne'] at this
  · intro i hi
    have : (i : ℝ) ≤ (nc : ℝ) := by exact_mod_cast hi
    rw [hx]
    nlinarith [hnc.1]
  · have hxN : x < (N : ℝ) + 1 - 7 := by
      have h1 : x * h < (L - 2 * η) := by linarith
      have h2 : (L - 2 * η) / h = (N : ℝ) + 1 - 2 * η / h := by rw [← hL]; field_simp
      have h3 : x < (L - 2 * η) / h := by rw [lt_div_iff₀ hh]; exact h1
      have h4 : 8 ≤ 2 * η / h := by rw [le_div_iff₀ hh]; linarith
      linarith
    have : (nc : ℝ) + 1 ≤ (N : ℝ) := by linarith [hnc.1]
    exact_mod_cast this

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.soft_geom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.soft_geom

end FormalResearch.JacobiEigenvectors.TheoremB

end
