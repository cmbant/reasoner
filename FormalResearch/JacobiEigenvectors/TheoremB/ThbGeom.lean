module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremB.SpliceSoft
public import FormalResearch.JacobiEigenvectors.TheoremB.ThbConstants

/-!
# Paper J, Theorem B, L3.5c, part 4: lattice geometry of the chart rows (pure real arithmetic)

The rows of the charts of the assembly are chosen from `nearestRow h x = round(x/h - 1/2)` (`u_n = (n + 1/2) h`).  This module collects the elementary facts about them that the assembly uses.

* `uNode_lt_iff`, `uNode_le_iff`, `uNode_add_one`: monotonicity of `n |-> u_n`.
* `nearestRow_bounds`: `x - h/2 <= u_{nearestRow h x} <= x + h/2`.
* `bulk_geom`: for a splice `s` in the open overlap `(c', c)` of a bulk chart (`c + sigma < L = (N+1) h`, `h` small): the splice row `n_s` satisfies `0 <= n_s`, `n_s + 1 <= N`, and the nodes of the rows
  `n_s`, `n_s + 1` lie in `[c', c]` (exterior rows of the two bulk charts).

Source: Paper J `app_thmB.tex`, proof of `prop:thb-inputs`, choice of the splice row and of the rows of the two bulk charts of a block.

## Differences from the paper

None (the paper's "`n_s` lies in the window" is made explicit: `h <= sigma`, `h <= 2 (c - s)/3`, `h <= 2 (s - c')`, `c + sigma < L`).

## Not formalised

Nothing.
-/

@[expose] public section

namespace FormalResearch.JacobiEigenvectors.TheoremB

open FormalResearch.JacobiEigenvectors.Setting

theorem uNode_lt_iff {h : ℝ} (hh : 0 < h) (a b : ℤ) : uNode h a < uNode h b ↔ a < b := by
  unfold uNode
  rw [mul_lt_mul_iff_left₀ hh]
  constructor
  · intro H
    have : (a : ℝ) < b := by linarith
    exact_mod_cast this
  · intro H
    have : (a : ℝ) < b := by exact_mod_cast H
    linarith

theorem uNode_le_iff {h : ℝ} (hh : 0 < h) (a b : ℤ) : uNode h a ≤ uNode h b ↔ a ≤ b := by
  rw [← not_lt, ← not_lt, uNode_lt_iff hh]

theorem uNode_add_one (h : ℝ) (n : ℤ) : uNode h (n + 1) = uNode h n + h := by
  unfold uNode; push_cast; ring

theorem nearestRow_bounds (h x : ℝ) (hh : 0 < h) : x - h / 2 ≤ uNode h (nearestRow h x) ∧ uNode h (nearestRow h x) ≤ x + h / 2 := by
  have := abs_le.mp (nearestRow_close h x hh)
  constructor <;> linarith [this.1, this.2]

theorem nonneg_of_uNode_pos {h : ℝ} (hh : 0 < h) {n : ℤ} (hn : 0 < uNode h n) : 0 ≤ n := by
  by_contra hcon
  push Not at hcon
  have h1 : (n : ℝ) ≤ -1 := by exact_mod_cast (show n ≤ -1 by omega)
  unfold uNode at hn
  nlinarith

/-- **Geometry of the splice row** of a bulk block. -/
theorem bulk_geom {h L c' c σ s : ℝ} {N : ℕ} (hh : 0 < h) (hLs : h * ((N : ℝ) + 1) = L) (hc' : 0 < c') (hs1 : c' < s) (hs2 : s < c)
    (hσ : 0 < σ) (hcL : c + σ < L) (h1 : h ≤ σ) (h2 : h ≤ 2 * (c - s) / 3) (h3 : h ≤ 2 * (s - c')) :
    0 ≤ nearestRow h s ∧ nearestRow h s + 1 ≤ (N : ℤ) ∧ uNode h (nearestRow h s + 1) ≤ c ∧ c' ≤ uNode h (nearestRow h s + 1) ∧
      c' ≤ uNode h (nearestRow h s) ∧ uNode h (nearestRow h s) ≤ c ∧ s < uNode h (nearestRow h s + 1) ∧ uNode h (nearestRow h s) ≤ s + h / 2 := by
  obtain ⟨b1, b2⟩ := nearestRow_bounds h s hh
  set ns := nearestRow h s with hns
  have hadd := uNode_add_one h ns
  have g1 : 0 ≤ ns := nonneg_of_uNode_pos hh (by linarith)
  have g3 : uNode h (ns + 1) ≤ c := by rw [hadd]; linarith
  refine ⟨g1, ?_, g3, by rw [hadd]; linarith, by linarith, by linarith, by rw [hadd]; linarith, b2⟩
  -- ns + 1 ≤ N
  by_contra hcon
  push Not at hcon
  have h4 : (N : ℝ) + 1 ≤ (ns : ℝ) + 1 := by
    have : (N : ℤ) + 1 ≤ ns + 1 := by omega
    exact_mod_cast this
  have h5 : uNode h (ns + 1) = ((ns : ℝ) + 1 + 1 / 2) * h := by unfold uNode; push_cast; ring
  rw [h5] at g3
  nlinarith

end FormalResearch.JacobiEigenvectors.TheoremB

end
